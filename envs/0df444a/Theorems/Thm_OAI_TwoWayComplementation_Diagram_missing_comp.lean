-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_missing_comp
-- name    : OAI.TwoWayComplementation.Diagram.missing_comp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:35:46.980645+00:00
-- url     : https://prove2.me/theorems/8609546b-069e-46f1-b701-290350c166a7
-- title:
--   A recurrent class lost in a product $zw$ is already lost in $z$ or in $w$
-- statement:
--   Fix $m\in\mathbb N$ and write $[m]=\{0,1,\dots,m-1\}$ for the set of labels. A *boundary diagram* $a$ on $[m]$ consists of four binary relations on $[m]$: the forward relation $F_a$ (enter on the left side, exit on the right side), the backward relation $B_a$ (enter on the right, exit on the left), the left return relation $L_a$ (enter and exit on the left) and the right return relation $R_a$ (enter and exit on the right). Relations are composed in path order, $XY=\{(x,z):\exists y\ (x,y)\in X,\ (y,z)\in Y\}$, and $X^*$ is the reflexive–transitive closure of $X$. The product $ab$ glues the right side of $a$ to the left side of $b$:
--   $$
--   \begin{aligned}
--   F_{ab}&=F_a\,(L_bR_a)^*\,F_b, & B_{ab}&=B_b\,(R_aL_b)^*\,B_a,\\
--   L_{ab}&=L_a\cup F_a\,(L_bR_a)^*\,L_b\,B_a, & R_{ab}&=R_b\cup B_b\,R_a\,(L_bR_a)^*\,F_b .
--   \end{aligned}
--   $$
--   This product is associative, and the diagrams on $[m]$ form a finite monoid whose identity is $(\Delta,\Delta,\varnothing,\varnothing)$, with $\Delta$ the equality relation. A diagram $z$ lies in the *corner* of a diagram $e$ if $ez=z$ and $ze=z$.
--
--   For a sign $s\in\{+,-\}$ the *through relation* of a diagram $a$ is $T^+_a=F_a$, $T^-_a=B_a$, and its *loop closure* is $K^+_a=(L_aR_a)^*$, $K^-_a=(R_aL_a)^*$. In a long product $\cdots aaa\cdots$, $K^s_a$ records finitely many back-and-forth bounces at the interface between two consecutive copies of $a$. For diagrams $e,z$, the *recurrence relation* of $e$ is $P^s_e=K^s_e\,T^s_e\,K^s_e$, and the *surviving relation* of a diagram $z$ relative to $e$ is $U^s_e(z)=K^s_e\,T^s_z\,K^s_e$: the traversal of $e$ is replaced by a traversal of $z$, while the loop closures of $e$ are kept. A *signed recurrent class* of $e$ is a pair $(s,C)$ with $C=\{y\in[m]:(x,y)\in P^s_e\text{ and }(y,x)\in P^s_e\}$ for some $x\in[m]$ with $(x,x)\in P^s_e$; let $\mathcal C(e)$ be the set of these pairs. The classes of $e$ *missing* in $z$ are those none of whose loops survives in $z$:
--   $$
--   \mathcal M_e(z)=\{(s,C)\in\mathcal C(e):\ (x,x)\notin U^s_e(z)\ \text{for every}\ x\in C\}.
--   $$
--
--   **Theorem.** Let $e$ be idempotent, $ee=e$, and let $z$ and $w$ lie in the corner of $e$, that is $ez=z=ze$ and $ew=w=we$. Then
--   $$
--   \mathcal M_e(zw)\subseteq\mathcal M_e(z)\cup\mathcal M_e(w).
--   $$
--
--   The corner of $e$ is closed under products, so the theorem can be iterated: for example $\mathcal M_e(z^n)\subseteq\mathcal M_e(z)$ for every $n\ge1$, and $\mathcal M_e(bgb)\subseteq\mathcal M_e(b)\cup\mathcal M_e(g)$ for $b,g$ in the corner. This is how the missing sets of a whole chain of products are kept inside one fixed budget of classes.
--
--   **Formalization Note** Signed classes are elements of `Bool × Set (Fin m)`; $\mathcal C(e)$ is `e.classes` and $\mathcal M_e(z)$ is `e.missing z`. The hypotheses are `comp e e = e`, `z ∈ e.corner` and `w ∈ e.corner`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean#L233-L249

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.missing_comp {m : ℕ} (e z w : Diagram m) (he : comp e e = e)
    (hz : z ∈ e.corner) (hw : w ∈ e.corner) :
    e.missing (comp z w) ⊆ e.missing z ∪ e.missing w := by sorry
