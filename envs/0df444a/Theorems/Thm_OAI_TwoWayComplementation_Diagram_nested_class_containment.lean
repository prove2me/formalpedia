-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_class_containment
-- name    : OAI.TwoWayComplementation.Diagram.nested_class_containment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:40:06.986707+00:00
-- url     : https://prove2.me/theorems/e4a2276a-5428-416f-931d-240743eb8c00
-- title:
--   Each recurrent class of a nested idempotent contains a surviving outer class or two distinct ones
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
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. For diagrams $e,z$, the *recurrence relation* of $e$ is $P^s_e=K^s_e\,T^s_e\,K^s_e$, and the *surviving relation* of a diagram $z$ relative to $e$ is $U^s_e(z)=K^s_e\,T^s_z\,K^s_e$: the traversal of $e$ is replaced by a traversal of $z$, while the loop closures of $e$ are kept. A *signed recurrent class* of $e$ is a pair $(s,C)$ with $C=\{y\in[m]:(x,y)\in P^s_e\text{ and }(y,x)\in P^s_e\}$ for some $x\in[m]$ with $(x,x)\in P^s_e$; let $\mathcal C(e)$ be the set of these pairs. The classes of $e$ *missing* in $z$ are those none of whose loops survives in $z$:
--   $$
--   \mathcal M_e(z)=\{(s,C)\in\mathcal C(e):\ (x,x)\notin U^s_e(z)\ \text{for every}\ x\in C\}.
--   $$
--
--   **Theorem.** Let $e$ and $d$ be idempotent diagrams with $ed=d$ and $de=d$ (so $d$ is nested below $e$), and let $(s,C)\in\mathcal C(d)$. Then at least one of the following holds:
--   1. there is a class $(s,C')\in\mathcal C(e)$ of the same sign with $C'\subseteq C$ and $(s,C')\notin\mathcal M_e(d)$;
--   2. there are two distinct classes $(s,C_1)\neq(s,C_2)$ in $\mathcal C(e)$, both of sign $s$, with $C_1\subseteq C$ and $C_2\subseteq C$.
--
--   Each recurrent class of the smaller idempotent $d$ therefore "pays" either with a class of $e$ that survives in $d$ or with two classes of $e$. Since classes are nonempty and distinct classes of $d$ with the same sign are disjoint, each class of $e$ is used by at most one class of $d$. This feeds a weighted counting argument (weight $1$ for classes of $e$ missing in $d$, weight $2$ for the others) that bounds the number of classes lost along a nested chain of idempotents.
--
--   **Formalization Note** Signed classes are elements of `Bool × Set (Fin m)`; $\mathcal C(a)$ is `a.classes` and $\mathcal M_e(d)$ is `e.missing d`. The hypotheses are `comp e e = e`, `comp d d = d` and `d ∈ e.corner`, and the two alternatives are stated with explicit sign equalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean#L199-L232

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.nested_class_containment {m : ℕ} (e d : Diagram m)
    (he : comp e e = e) (hd : comp d d = d) (hde : d ∈ e.corner)
    {c : Bool × Set (Fin m)} (hc : c ∈ d.classes) :
    (∃ C ∈ e.classes, C.1 = c.1 ∧ C.2 ⊆ c.2 ∧ C ∉ e.missing d) ∨
      ∃ C ∈ e.classes, ∃ D ∈ e.classes,
        C ≠ D ∧ C.1 = c.1 ∧ D.1 = c.1 ∧ C.2 ⊆ c.2 ∧ D.2 ⊆ c.2 := by sorry
