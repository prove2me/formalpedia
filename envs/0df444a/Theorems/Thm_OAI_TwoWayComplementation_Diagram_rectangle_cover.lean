-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_rectangle_cover
-- name    : OAI.TwoWayComplementation.Diagram.rectangle_cover
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:37:02.941123+00:00
-- url     : https://prove2.me/theorems/b6b3e9c4-f7aa-44d9-959b-d7342e6e948e
-- title:
--   Every through edge of an idempotent diagram lies in the rectangle of a recurrent point
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. Let $P^s_e=K^s_eT^s_eK^s_e$ be the recurrence relation of $e$. A point $p\in[m]$ is *recurrent* if $(p,p)\in P^s_e$, and the *rectangle* of $p$ is $\mathrm{Rect}^s_e(p)=\{u:(u,p)\in T^s_eK^s_e\}\times\{v:(p,v)\in K^s_eT^s_e\}$.
--
--   **Theorem.** Let $e$ be idempotent, $ee=e$, let $s$ be a sign, and let $(u,v)\in T^s_e$. Then $(u,v)$ lies in the rectangle of some recurrent point:
--   $$
--   \exists\,p\in[m]:\qquad (p,p)\in P^s_e,\qquad (u,p)\in T^s_eK^s_e,\qquad (p,v)\in K^s_eT^s_e .
--   $$
--
--   Thus the through relation of an idempotent diagram is covered by the rectangles of its recurrent points. The statement holds for every $m$, including $m=0$, where it is vacuous. It is used to show that an element of the corner of $e$ that loses no recurrent class keeps all through edges of $e$, and to locate recurrent points of $e$ on the recurrent loops of a diagram nested below $e$.
--
--   **Formalization Note** Labels are elements of `Fin m`, the rectangle is `e.rectangle s p`, and idempotence is the hypothesis `comp e e = e`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L314-L328

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.rectangle_cover {m : ℕ} (e : Diagram m) (he : comp e e = e)
    {positive : Bool} {u v : Fin m} (huv : (u, v) ∈ e.through positive) :
    ∃ p, (p, p) ∈ e.recurrence positive ∧ (u, v) ∈ e.rectangle positive p := by sorry
