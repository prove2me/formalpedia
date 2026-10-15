-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_corner_forward_absorption
-- name    : OAI.TwoWayComplementation.Diagram.corner_forward_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:32:50.036674+00:00
-- url     : https://prove2.me/theorems/93966e45-11c8-4c19-ac77-d96a5acbe03a
-- title:
--   Forward traversals of a corner element absorb forward traversals of the outer diagram
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
--   Let $e$ and $z$ be boundary diagrams on $[m]$ such that $z$ lies in the *corner* of $e$, that is,
--   $$
--   ez=z\qquad\text{and}\qquad ze=z
--   $$
--   ($e$ is not assumed to be idempotent). Write $K^+_e=(L_eR_e)^*$ for the forward loop closure of $e$.
--
--   **Theorem.** Under these assumptions
--   $$
--   F_e\,K^+_e\,F_z\subseteq F_z\qquad\text{and}\qquad F_z\,K^+_e\,F_e\subseteq F_z .
--   $$
--
--   So a left-to-right traversal of $z$ remains a left-to-right traversal of $z$ when it is preceded, or followed, by a left-to-right traversal of $e$ joined to it by finitely many returns of $e$ at the interface. This is the positive-sign case of the absorption property of corners, from which one derives that surviving relations of corner elements absorb the recurrence relation of $e$.
--
--   **Formalization Note** $K^+_e$ is `e.loopClosure true`, and the corner hypothesis is `z ∈ e.corner`, which unfolds to `comp e z = z` and `comp z e = z`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L77-L92

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.corner_forward_absorption {m : ℕ} (e z : Diagram m) (hz : z ∈ e.corner) :
    e.forward ○ e.loopClosure true ○ z.forward ⊆ z.forward ∧
    z.forward ○ e.loopClosure true ○ e.forward ⊆ z.forward := by sorry
