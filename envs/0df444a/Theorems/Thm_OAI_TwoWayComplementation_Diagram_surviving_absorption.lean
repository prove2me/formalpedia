-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_surviving_absorption
-- name    : OAI.TwoWayComplementation.Diagram.surviving_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:34:30.601877+00:00
-- url     : https://prove2.me/theorems/5d3ac8dc-5ed9-44dd-8803-ae9d12fd676e
-- title:
--   Surviving relations of corner elements absorb the recurrence relation on both sides
-- statement:
--   Fix $m\in\mathbb N$ and write $[m]=\{0,1,\dots,m-1\}$ for the set of labels. A *boundary diagram* $a$ on $[m]$ consists of four binary relations on $[m]$: the forward relation $F_a$ (enter on the left side, exit on the right side), the backward relation $B_a$ (enter on the right, exit on the left), the left return relation $L_a$ (enter and exit on the left) and the right return relation $R_a$ (enter and exit on the right). Relations are composed in path order, $XY=\{(x,z):\exists y\ (x,y)\in X,\ (y,z)\in Y\}$, and $X^*$ is the reflexive–transitive closure of $X$. The product $ab$ glues the right side of $a$ to the left side of $b$:
--   $$
--   \begin{aligned}
--   F_{ab}&=F_a\,(L_bR_a)^*\,F_b, & B_{ab}&=B_b\,(R_aL_b)^*\,B_a,\\
--   L_{ab}&=L_a\cup F_a\,(L_bR_a)^*\,L_b\,B_a, & R_{ab}&=R_b\cup B_b\,R_a\,(L_bR_a)^*\,F_b .
--   \end{aligned}
--   $$
--   This product is associative, and the diagrams on $[m]$ form a finite monoid whose identity is $(\Delta,\Delta,\varnothing,\varnothing)$, with $\Delta$ the equality relation.
--
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. For diagrams $e,z$ define the recurrence relation of $e$ and the surviving relation of $z$ relative to $e$ by
--   $$
--   P^s_e=K^s_e\,T^s_e\,K^s_e,\qquad U^s_e(z)=K^s_e\,T^s_z\,K^s_e ;
--   $$
--   thus $U^s_e(z)$ is obtained from $P^s_e$ by replacing the traversal of $e$ with a traversal of $z$, keeping the loop closures of $e$.
--
--   **Theorem.** If $z$ lies in the corner of $e$, i.e. $ez=z$ and $ze=z$ ($e$ need not be idempotent), then for both signs $s$
--   $$
--   P^s_e\,U^s_e(z)\subseteq U^s_e(z)\qquad\text{and}\qquad U^s_e(z)\,P^s_e\subseteq U^s_e(z) .
--   $$
--
--   Consequently $P^s_e\,U^s_e(z)\,P^s_e\subseteq U^s_e(z)$. In particular, if $(x,y)$ and $(y,x)$ lie in $P^s_e$ and $(x,x)\in U^s_e(z)$, then also $(y,y)\in U^s_e(z)$: whether a recurrent loop of $e$ survives in $z$ depends only on its recurrent class. This is what allows a class of $e$ to be declared missing in $z$ by testing a single representative.
--
--   **Formalization Note** $P^s_e$ is `e.recurrence s`, $U^s_e(z)$ is `e.surviving z s`, and the hypothesis is `z ∈ e.corner`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L125-L142

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.surviving_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ e.surviving z positive ⊆ e.surviving z positive ∧
    e.surviving z positive ○ e.recurrence positive ⊆ e.surviving z positive := by sorry
