-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_recurrence_idempotent
-- name    : OAI.TwoWayComplementation.Diagram.recurrence_idempotent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:31:07.188159+00:00
-- url     : https://prove2.me/theorems/626ef309-c84e-4285-9fb4-521ac2106140
-- title:
--   The recurrence relation of an idempotent boundary diagram is idempotent
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. The *recurrence relation* of a diagram $e$ is
--   $$
--   P^s_e=K^s_e\,T^s_e\,K^s_e ;
--   $$
--   for instance, $(x,y)\in P^+_e$ means that in a long product of copies of $e$ one can go from $x$ to $y$ by bouncing at an interface, traversing one copy of $e$ from left to right, and bouncing at the next interface.
--
--   **Theorem.** Let $e$ be an idempotent boundary diagram, $ee=e$. Then for both signs $s$,
--   $$
--   P^s_e\,P^s_e=P^s_e .
--   $$
--
--   In particular $P^s_e$ is transitive, so mutual $P^s_e$-reachability is an equivalence relation on the points $x$ with $(x,x)\in P^s_e$; its equivalence classes are the signed recurrent classes of $e$. Idempotence of $P^s_e$ is also the input for factoring pairs of $P^s_e$ through recurrent points, and hence for covering the through edges of $e$ by rectangles of recurrent points.
--
--   **Formalization Note** The sign is a Boolean `positive` (`true` for $+$); $T^s_e$, $K^s_e$ and $P^s_e$ are `through`, `loopClosure` and `recurrence`, and idempotence is the hypothesis `comp e e = e`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L53-L67

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.recurrence_idempotent {m : ℕ} (e : Diagram m) (he : comp e e = e)
    (positive : Bool) :
    e.recurrence positive ○ e.recurrence positive = e.recurrence positive := by sorry
