-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_corner_through_absorption
-- name    : OAI.TwoWayComplementation.Diagram.corner_through_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:33:43.085637+00:00
-- url     : https://prove2.me/theorems/b6743811-d1ab-426d-bff9-edfde186ad64
-- title:
--   Through-relation absorption in the corner of a boundary diagram, for both signs
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. Let $e$ and $z$ be diagrams such that $z$ lies in the corner of $e$:
--   $$
--   ez=z\qquad\text{and}\qquad ze=z
--   $$
--   ($e$ need not be idempotent).
--
--   **Theorem.** For both signs $s$,
--   $$
--   T^s_e\,K^s_e\,T^s_z\subseteq T^s_z\qquad\text{and}\qquad T^s_z\,K^s_e\,T^s_e\subseteq T^s_z .
--   $$
--
--   For $s=+$ this is forward absorption in a corner; for $s=-$ it says that a right-to-left traversal of $z$ absorbs right-to-left traversals of $e$ on either side, joined by returns of $e$. The sign-uniform form is the one used for recurrence and surviving relations, so that the later arguments about recurrent classes can be carried out once for a sign parameter $s$.
--
--   **Formalization Note** The sign is the Boolean `positive`; $T^s$ and $K^s$ are `through` and `loopClosure`, and the hypothesis is `z ∈ e.corner`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L94-L113

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.corner_through_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner)
    (positive : Bool) :
    e.through positive ○ e.loopClosure positive ○ z.through positive ⊆ z.through positive ∧
    z.through positive ○ e.loopClosure positive ○ e.through positive ⊆ z.through positive := by sorry
