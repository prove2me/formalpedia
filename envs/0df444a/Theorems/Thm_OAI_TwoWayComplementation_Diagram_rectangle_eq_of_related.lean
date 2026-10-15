-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_rectangle_eq_of_related
-- name    : OAI.TwoWayComplementation.Diagram.rectangle_eq_of_related
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:36:14.910434+00:00
-- url     : https://prove2.me/theorems/8c165502-8d0d-4b9d-9a07-6a4727608cb2
-- title:
--   Mutually recurrent points of an idempotent diagram have the same rectangle
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. Let $P^s_e=K^s_eT^s_eK^s_e$ be the recurrence relation of $e$. For $p\in[m]$ the *rectangle* of $p$ is the product set
--   $$
--   \mathrm{Rect}^s_e(p)=\{u\in[m]:(u,p)\in T^s_eK^s_e\}\times\{v\in[m]:(p,v)\in K^s_eT^s_e\},
--   $$
--   viewed as a relation on $[m]$.
--
--   **Theorem.** Let $e$ be idempotent, $ee=e$, let $s$ be a sign, and let $p,q\in[m]$ satisfy $(p,q)\in P^s_e$ and $(q,p)\in P^s_e$. Then
--   $$
--   \mathrm{Rect}^s_e(p)=\mathrm{Rect}^s_e(q).
--   $$
--
--   Hence the rectangle depends only on the signed recurrent class of $p$, and every signed recurrent class of an idempotent diagram has a well-defined rectangle. (Since $T^s_eK^s_eT^s_e=T^s_e$ for idempotent $e$, each rectangle consists of through edges of $e$.) Class rectangles are used to account for the through edges of $e$ that are lost when $e$ is replaced by another element of its corner.
--
--   **Formalization Note** $\mathrm{Rect}^s_e(p)$ is `e.rectangle s p`, defined as a product set of two subsets of `Fin m`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L290-L312

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.rectangle_eq_of_related {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {p q : Fin m} (hpq : (p, q) ∈ e.recurrence positive)
    (hqp : (q, p) ∈ e.recurrence positive) :
    e.rectangle positive p = e.rectangle positive q := by sorry
