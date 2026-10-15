-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_forward_loop_absorption
-- name    : OAI.TwoWayComplementation.Diagram.nested_forward_loop_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:37:28.775089+00:00
-- url     : https://prove2.me/theorems/b23d3e38-2315-4697-9998-51f779099635
-- title:
--   Forward edges of the outer diagram are absorbed by the loop closure of a corner element
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
--   Let $e$ and $d$ be diagrams such that $d$ lies in the corner of $e$, i.e.
--   $$
--   ed=d\qquad\text{and}\qquad de=d
--   $$
--   (neither is assumed to be idempotent), and let $K^+_d=(L_dR_d)^*$ be the forward loop closure of $d$.
--
--   **Theorem.** Under these assumptions
--   $$
--   F_e\,K^+_d\,F_d\subseteq K^+_d\,F_d\qquad\text{and}\qquad F_d\,K^+_d\,F_e\subseteq F_d\,K^+_d .
--   $$
--
--   In words: putting a forward traversal of $e$ in front of a path "bounces of $d$, then a forward traversal of $d$" gives a path of the same shape, and symmetrically on the right. Unlike forward absorption in a corner, where the bounces are those of $e$, here they are the bounces of the corner element $d$ itself. This is the form needed to show that the recurrence relation of $d$ absorbs traversals of $e$, and hence the recurrence relation of $e$.
--
--   **Formalization Note** $K^+_d$ is `d.loopClosure true`, and the hypothesis is `d ∈ e.corner`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean#L18-L85

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.nested_forward_loop_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner) :
    e.forward ○ d.loopClosure true ○ d.forward ⊆ d.loopClosure true ○ d.forward ∧
    d.forward ○ d.loopClosure true ○ e.forward ⊆ d.forward ○ d.loopClosure true := by sorry
