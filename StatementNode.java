package tree;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;

import source.Position;
import syms.Scope;
import syms.SymEntry;
import syms.Type;

/** 
 * class StatementNode - Abstract syntax tree representation of statements. 
 * @version $Revision: 17 $  $Date: 2013-05-13 08:25:39 +1000 (Mon, 13 May 2013) $
 * Classes defined within StatementNode extend it.
 * All statements have a position within the original source code.
 */
public abstract class StatementNode {
    /** Position in the input source program */
    private Position pos;

    /** Constructor */
    protected StatementNode( Position pos ) {
        this.pos = pos;
    }
    protected Position getPosition() {
        return pos;
    }
    /** All statement nodes provide an accept method to implement the visitor
     * pattern to traverse the tree.
     * @param visitor class implementing the details of the particular
     *  traversal.
     */
    public abstract void accept( StatementVisitor visitor );
    /** All statement nodes provide a genCode method to implement the visitor
     * pattern to traverse the tree for code generation.
     * @param visitor class implementing the code generation
     */
    public abstract Code genCode( StatementTransform<Code> visitor );

    /** Statement node representing an erroneous statement. */
    public static class ErrorNode extends StatementNode {
        public ErrorNode( Position pos ) {
            super( pos );
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitStatementErrorNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitStatementErrorNode( this );
        }
        @Override
        public String toString() {
            return "ERROR";
        }
    }

    /** Tree node representing an assignment statement. */
    public static class AssignmentNode extends StatementNode {
        /** Tree node for expression(s) on left hand side of an assignment. */
        private ArrayList<ExpNode> variables;
        /** Tree node for the expression(s) to be assigned. */
        private ArrayList<ExpNode> exps;

        public AssignmentNode( Position pos, ExpNode variable, 
                ExpNode exp ) {
            super( pos );
            this.variables = new ArrayList<ExpNode>();
            this.exps = new ArrayList<ExpNode>();
            this.variables.add(variable);
            this.exps.add(exp);
        }
        
        /** Assumes length of variables and exps matches */
        public AssignmentNode( Position pos, ArrayList<ExpNode> variables, 
                ArrayList<ExpNode> exps ) {
            super( pos );
            this.variables = variables;
            this.exps = exps;
            if( variables.size() != exps.size() ) {
                throw new ArrayIndexOutOfBoundsException(
                        "AssignmentNode variables/expressions count mismatch");
            }
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitAssignmentNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitAssignmentNode( this );
        }
        public ArrayList<ExpNode> getVariables() {
            return variables;
        }
        public void setVariables( ArrayList<ExpNode> variables ) {
            this.variables = variables;
        }
        public ArrayList<ExpNode> getExps() {
            return exps;
        }
        public void setExps(ArrayList<ExpNode> exps) {
            this.exps = exps;
        }
        public ArrayList<String> getVariableNames() {
            ArrayList<String> vNames = new ArrayList<String>();
            for( ExpNode v : this.variables ) {
                if( v instanceof ExpNode.VariableNode ) {
                    vNames.add( ( (ExpNode.VariableNode)v ).getId() );
                } else {
                    vNames.add( "<noname>" );
                }
            }
            return vNames;
        }
        @Override
        public String toString( ) {
            String varNames = "";
            String expStrings = "";
            for( ExpNode v : this.variables ){
                if (varNames.length() > 0) {
                    varNames += ", ";
                }
                varNames += v.toString();
            }
            for( ExpNode e : this.exps ){
                if (expStrings.length() > 0) {
                    expStrings += ", ";
                }
                expStrings += e.toString();
            }
            return varNames + " := " + expStrings;
        }
    }

    /** Tree node representing a "write" statement. */
    public static class WriteNode extends StatementNode {
        private ExpNode exp;

        public WriteNode( Position pos, ExpNode exp ) {
            super( pos );
            this.exp = exp;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitWriteNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitWriteNode( this );
        }
        public ExpNode getExp() {
            return exp;
        }
        public void setExp( ExpNode exp ) {
            this.exp = exp;
        }
        @Override
        public String toString( ) {
            return "WRITE " + exp.toString();
        }
    }
    
    /** Tree node representing a "call" statement. */
    public static class CallNode extends StatementNode {
        private String id;
        private SymEntry.ProcedureEntry procEntry;

        public CallNode( Position pos, String id ) {
            super( pos );
            this.id = id;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitCallNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitCallNode( this );
        }
        public String getId() {
            return id;
        }
        public SymEntry.ProcedureEntry getEntry() {
            return procEntry;
        }
        public void setEntry(SymEntry.ProcedureEntry entry) {
            this.procEntry = entry;
        }
        @Override
        public String toString( ) {
            String s = "CALL " + procEntry.getIdent() + "(";
            return s + ")";
        }
    }
    /** Tree node representing a statement list. */
    public static class ListNode extends StatementNode {
        private List<StatementNode> statements;
        
        public ListNode( Position pos ) {
            super( pos );
            this.statements = new ArrayList<StatementNode>();
        }
        public void addStatement( StatementNode s ) {
            statements.add( s );
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitStatementListNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitStatementListNode( this );
        }
        public List<StatementNode> getStatements() {
            return statements;
        }
        @Override
        public String toString() {
            String result = "";
            String sep = "";
            for( StatementNode s : statements ) {
                result += sep + s.toString();
                sep = "; ";
            }
            return result;
        }
    }
    /** Tree node representing an "if" statement. */
    public static class IfNode extends StatementNode {
        private ExpNode condition;
        private StatementNode thenStmt;
        private StatementNode elseStmt;

        public IfNode( Position pos, ExpNode condition, 
                StatementNode thenStmt, StatementNode elseStmt ) {
            super( pos );
            this.condition = condition;
            this.thenStmt = thenStmt;
            this.elseStmt = elseStmt;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitIfNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitIfNode( this );
        }
        public ExpNode getCondition() {
            return condition;
        }
        public void setCondition( ExpNode cond ) {
            this.condition = cond;
        }
        public StatementNode getThenStmt() {
            return thenStmt;
        }
        public StatementNode getElseStmt() {
            return elseStmt;
        }
        @Override
        public String toString( ) {
            return "IF " + condition.toString() + " THEN " + thenStmt +
                " ELSE " + elseStmt;
        }
    }
    
    /** Tree node representing a "skip" statement. */
    public static class SkipNode extends StatementNode {
        public SkipNode( Position pos ) {
            super( pos );
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitSkipNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitSkipNode( this );
        }
        @Override
        public String toString() {
            return "SKIP";
        }
    }
    
    /** Tree node representing a "for" statement. */
    public static class ForNode extends StatementNode {
        private StatementNode loopStmt;
        private ExpNode startCond;
        private ExpNode endCond;
        private ExpNode controlVar;
        private Scope localScope;
        
        public ForNode( Position pos, ExpNode controlVar,
                ExpNode startCondition, ExpNode endCondition, 
                StatementNode loopStatement, Scope localScope ) {
            super( pos );
            this.controlVar = controlVar;
            this.startCond = startCondition;
            this.endCond = endCondition;
            this.loopStmt= loopStatement;
            this.localScope = localScope;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitForNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitForNode( this );
        }
        public ExpNode getControlVar() {
            return controlVar;
        }
        public void setControlVar( ExpNode controlVar ) {
            this.controlVar = controlVar;
        }        
        public Scope getLocalScope() {
            return localScope;
        }
        public void setLocalScope( Scope scope ) {
            this.localScope = scope;
        }        
        public ExpNode getStartCondition() {
            return startCond;
        }
        public void setStartCondition( ExpNode cond ) {
            this.startCond = cond;
        }
        public ExpNode getEndCondition() {
            return endCond;
        }
        public void setEndCondition( ExpNode cond ) {
            this.endCond = cond;
        }
        public StatementNode getLoopStmt() {
            return loopStmt;
        }
        @Override
        public String toString( ) {
            return "FOR " + controlVar.toString() + ": [" + 
                    startCond.toString() + ".." + 
                    endCond.toString() + "] DO " + loopStmt.toString();
        }
    }

    /** Tree node representing a "while" statement. */
    public static class WhileNode extends StatementNode {
        private ExpNode condition;
        private StatementNode loopStmt;

        public WhileNode( Position pos, ExpNode condition, 
              StatementNode loopStmt ) {
            super( pos );
            this.condition = condition;
            this.loopStmt = loopStmt;
        }
        @Override
        public void accept( StatementVisitor visitor ) {
            visitor.visitWhileNode( this );
        }
        @Override
        public Code genCode( StatementTransform<Code> visitor ) {
            return visitor.visitWhileNode( this );
        }
        public ExpNode getCondition() {
            return condition;
        }
        public void setCondition( ExpNode cond ) {
            this.condition = cond;
        }
        public StatementNode getLoopStmt() {
            return loopStmt;
        }
        @Override
        public String toString( ) {
            return "WHILE " + condition.toString() + " DO " +
                loopStmt.toString();
        }
    }
}

