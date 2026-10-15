-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_exists_nested_chain
-- name    : OAI.TwoWayComplementation.exists_nested_chain
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:41:36.769766+00:00
-- url     : https://prove2.me/theorems/d8173180-3fdb-46ea-9541-d93be07e391e
-- title:
--   A nested chain of idempotents in a finite monoid whose class losses total at most $2|J|$
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
--   For idempotent diagrams $d,e$ write $d\preceq e$ (*nesting*) if $de=d$ and $ed=d$.
--
--   **Theorem.** Let $A$ be a finite monoid, $k\in\mathbb N$, and let $\iota$ be a multiplicative map from $A$ to the monoid of boundary diagrams on $[m]$, i.e. $\iota(xy)=\iota(x)\iota(y)$ ($\iota(1)$ need not be the identity diagram). Let $a_0\in A$ be idempotent, let $g_0,g_1,\dots\in A$, and let $J$ be a set of pairs $(s,C)$ with $s$ a sign and $C\subseteq[m]$. Put $e_0=\iota(a_0)$ and assume that for every $j<k$, $\iota(g_j)$ lies in the corner of $e_0$ and $\mathcal M_{e_0}(\iota(g_j))\subseteq J$. Then there is a sequence $b_0,b_1,\dots$ in $A$ such that
--   1. $b_0=a_0$;
--   2. every $b_j$ is idempotent;
--   3. for every $j$ there is $n\in\mathbb N$ with $b_{j+1}=(b_jg_jb_j)^{n+1}$;
--   4. for every $j$, $\iota(b_{j+1})\preceq\iota(b_j)$;
--   5. for every $j\le k$, $\mathcal M_{e_0}(\iota(b_j))\subseteq J$;
--   6. the total loss along the first $k$ steps obeys the bound displayed below:
--
--   $$
--   \sum_{j=0}^{k-1}\big|\mathcal M_{\iota(b_j)}(\iota(b_{j+1}))\big|\le 2\,|J| .
--   $$
--
--   Each step sandwiches the next element $g_j$ between two copies of the current idempotent and passes to an idempotent power, so the chain descends in the nesting order while absorbing $g_0,g_1,\dots$ one after another. If each single perturbation $g_j$ loses only classes from a fixed budget $J$ relative to the starting idempotent, then the losses along the whole chain sum to at most $2|J|$. In the complementation argument this upper bound on the total loss is played off against lower bounds for the losses of the individual steps.
--
--   **Formalization Note** $\iota$ is a non-unital multiplicative map `A →ₙ* Diagram m`, the monoid structure on diagrams having multiplication `comp`; idempotence in $A$ is `IsIdempotentElem`, and nesting is membership in `Diagram.nesting m`, which includes idempotence of both diagrams. Properties 2–4 hold for every $j\in\mathbb N$, while the hypotheses on $g_j$ are only needed for $j<k$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean#L34-L97

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners

open OAI OAI.TwoWayComplementation
open scoped SetRel

theorem OAI.TwoWayComplementation.exists_nested_chain {A : Type*} [Monoid A] [Finite A] {m k : ℕ}
    (ι : A →ₙ* Diagram m) (b0 : A) (hb0 : IsIdempotentElem b0) (g : ℕ → A)
    (J : Set (Bool × Set (Fin m)))
    (hg : ∀ j < k, ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J) :
    ∃ b : ℕ → A, b 0 = b0 ∧
      (∀ j, IsIdempotentElem (b j)) ∧
      (∀ j, ∃ n : ℕ, b (j + 1) = (b j * g j * b j) ^ (n + 1)) ∧
      (∀ j, (ι (b (j + 1)), ι (b j)) ∈ Diagram.nesting m) ∧
      (∀ j ≤ k, (ι b0).missing (ι (b j)) ⊆ J) ∧
      ∑ j ∈ Finset.range k, ((ι (b j)).missing (ι (b (j + 1)))).ncard ≤ 2 * J.ncard := by sorry
