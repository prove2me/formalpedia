-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_recurrence_absorption
-- name    : OAI.TwoWayComplementation.Diagram.nested_recurrence_absorption
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:38:20.136637+00:00
-- url     : https://prove2.me/theorems/3b9b3aee-37f6-4132-b75d-9aedd7d1a41e
-- title:
--   Recurrence of a corner element absorbs recurrence of the outer diagram
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. The recurrence relation of a diagram $a$ is $P^s_a=K^s_aT^s_aK^s_a$.
--
--   **Theorem.** Let $e,d$ be diagrams with $ed=d$ and $de=d$ (no idempotence is assumed). Then for both signs $s$,
--   $$
--   P^s_e\,P^s_d\subseteq P^s_d\qquad\text{and}\qquad P^s_d\,P^s_e\subseteq P^s_d .
--   $$
--
--   So recurrence of the outer diagram $e$ is absorbed on either side by recurrence of the corner element $d$. In particular, if $x$ and $p$ are mutually $P^s_d$-related, then every point that is mutually $P^s_e$-related to $p$ is mutually $P^s_d$-related to $x$. This is how the recurrent classes of an idempotent $e$ are shown to sit inside the recurrent classes of an idempotent $d$ nested below it.
--
--   **Formalization Note** $P^s_a$ is `a.recurrence s`, and the hypothesis is `d ∈ e.corner`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean#L110-L133

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.nested_recurrence_absorption {m : ℕ} (e d : Diagram m) (hd : d ∈ e.corner)
    (positive : Bool) :
    e.recurrence positive ○ d.recurrence positive ⊆ d.recurrence positive ∧
    d.recurrence positive ○ e.recurrence positive ⊆ d.recurrence positive := by sorry
