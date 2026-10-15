-- Prove2me | Theorems.Thm_OAI_TwoWayComplementation_Diagram_nested_chain_bound
-- name    : OAI.TwoWayComplementation.Diagram.nested_chain_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T08:41:05.127993+00:00
-- url     : https://prove2.me/theorems/453aa744-606a-4995-8d30-880328ba776d
-- title:
--   Along a nested chain of idempotent diagrams the lost classes total at most $2|J|$
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
--   For idempotents $d,e$ write $d\preceq e$ (*nesting*) if $de=d$ and $ed=d$.
--
--   **Theorem.** Let $k\in\mathbb N$ and let $b_0,b_1,b_2,\dots$ be boundary diagrams on $[m]$ such that
--   - $b_j$ is idempotent for every $j\le k$;
--   - $b_{j+1}\preceq b_j$, i.e. $b_{j+1}b_j=b_{j+1}=b_jb_{j+1}$, for every $j<k$.
--
--   Let $J$ be any set of pairs $(s,C)$ with $s$ a sign and $C\subseteq[m]$, such that $\mathcal M_{b_0}(b_j)\subseteq J$ for every $j\le k$. Then
--   $$
--   \sum_{j=0}^{k-1}\big|\mathcal M_{b_j}(b_{j+1})\big|\le 2\,|J| .
--   $$
--
--   The individual losses $\mathcal M_{b_j}(b_{j+1})$ are measured relative to the current idempotent $b_j$, while the hypothesis only controls losses relative to the initial idempotent $b_0$. The theorem says that one common budget $J$ for the latter pays, up to a factor $2$, for all of the former together. This amortized bound is applied to descending chains of idempotents built from products in a finite monoid.
--
--   **Formalization Note** The chain is a function `b : ℕ → Diagram m`, of which only $b_0,\dots,b_k$ matter; nesting is membership in `nesting m`, and cardinalities are `Set.ncard`, which are true cardinalities here because there are only finitely many pairs $(s,C)$. The set $J$ is not required to consist of classes of $b_0$, and for $k=0$ the sum is empty.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Nesting.lean#L265-L346

import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

open OAI OAI.TwoWayComplementation OAI.TwoWayComplementation.Diagram
open scoped SetRel

theorem OAI.TwoWayComplementation.Diagram.nested_chain_bound {m k : ℕ} (b : ℕ → Diagram m)
    (hidemp : ∀ j ≤ k, comp (b j) (b j) = b j)
    (hnest : ∀ j < k, (b (j + 1), b j) ∈ nesting m)
    (J : Set (Bool × Set (Fin m)))
    (hJ : ∀ j ≤ k, (b 0).missing (b j) ⊆ J) :
    ∑ j ∈ Finset.range k, ((b j).missing (b (j + 1))).ncard ≤ 2 * J.ncard := by sorry
