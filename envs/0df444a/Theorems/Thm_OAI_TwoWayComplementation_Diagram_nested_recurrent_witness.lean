-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_recurrent_witness
-- name    : OAI.TwoWayComplementation.Diagram.nested_recurrent_witness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:39:10.939694+00:00
-- url     : https://prove2.me/theorems/07006402-5996-42c5-835e-2195f923fa28
-- title:
--   A recurrent loop of a corner element passes through two recurrent points of the outer idempotent
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. The recurrence relation of a diagram $a$ is $P^s_a=K^s_aT^s_aK^s_a$, and the surviving relation of $d$ relative to $e$ is $U^s_e(d)=K^s_eT^s_dK^s_e$.
--
--   **Theorem.** Let $e$ be idempotent ($ee=e$) and let $d$ lie in the corner of $e$ ($ed=d$ and $de=d$; $d$ need not be idempotent). Let $s$ be a sign and $x\in[m]$ with $(x,x)\in P^s_d$. Then there are $p,q\in[m]$ such that
--   $$
--   (p,p),\,(q,q)\in P^s_e,\qquad (x,p),\,(p,x),\,(x,q),\,(q,x)\in P^s_d,\qquad (p,q)\in U^s_e(d).
--   $$
--
--   So every recurrent loop of $d$ meets two recurrent points $p,q$ of $e$, both mutually $P^s_d$-related to $x$, and $p$ leads to $q$ by a single traversal of $d$ framed by loop closures of $e$. This yields the dichotomy for nested idempotents: the recurrent class of $x$ in $d$ contains the recurrent classes of $p$ and of $q$ in $e$, and if these two classes coincide, the class of $p$ survives in $d$.
--
--   **Formalization Note** Labels are elements of `Fin m`; the hypotheses are `comp e e = e` and `d ∈ e.corner`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean#L169-L197

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.nested_recurrent_witness {m : ℕ} (e d : Diagram m) (he : comp e e = e)
    (hd : d ∈ e.corner) {positive : Bool} {x : Fin m}
    (hxx : (x, x) ∈ d.recurrence positive) :
    ∃ p q, (p, p) ∈ e.recurrence positive ∧ (q, q) ∈ e.recurrence positive ∧
      (x, p) ∈ d.recurrence positive ∧ (p, x) ∈ d.recurrence positive ∧
      (x, q) ∈ d.recurrence positive ∧ (q, x) ∈ d.recurrence positive ∧
      (p, q) ∈ e.surviving d positive := by sorry
