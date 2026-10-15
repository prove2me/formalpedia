-- Prove2me | Theorems.Thm_OAI_OneWayLiveness_Pairing_support_sandwich_subset_marked
-- name    : OAI.OneWayLiveness.Pairing.support_sandwich_subset_marked
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:58.381501+00:00
-- url     : https://prove2.me/theorems/8e0877ed-6a9f-423a-b57f-c33f37f9ccbb
-- title:
--   Sandwiching by a split pair confines the support of a perturbed identity to the marked strands
-- statement:
--   For finite sets $X$ and $Y$, a *diagram* $a\in\mathcal P(X,Y)$ is a perfect matching of $X\sqcup Y$, with left ports $X$ and right ports $Y$. Diagrams compose by gluing. For $a\in\mathcal P(X,Y)$ and $b\in\mathcal P(Y,Z)$, the glued graph $\Gamma(a,b)$ has vertex set $(X\sqcup Y)\sqcup(Y\sqcup Z)$ and three kinds of edges: the matched pairs of $a$, the matched pairs of $b$, and one interface edge joining the two copies of each $y\in Y$. The composite $a\cdot b\in\mathcal P(X,Z)$ matches two distinct outer ports iff they are connected in $\Gamma(a,b)$; closed loops are discarded. The identity $\mathrm{id}_X$ matches each left port $x$ with the right port $x$. The *support* $\operatorname{supp}(a)$ of $a\in\mathcal P(X,X)$ is the set of $x\in X$ whose left copy is not matched to its right copy.
--
--   Let $A$ and $B$ be finite sets, and let $v\in\mathcal P(A,B)$ and $u\in\mathcal P(B,A)$ satisfy $v\cdot u=\mathrm{id}_A$. Let $J\subseteq B$. The *marked set* $\mathrm{mk}(v,u,J)\subseteq A$ consists of those $x\in A$ for which, in $\Gamma(v,u)$, the outer left port $x$ is connected to the copy on $v$'s side of some interface point $i\in J$.
--
--   **Theorem.** For every $a\in\mathcal P(B,B)$ with $\operatorname{supp}(a)\subseteq J$,
--   $$
--   \operatorname{supp}\big((v\cdot a)\cdot u\big)\ \subseteq\ \mathrm{mk}(v,u,J).
--   $$
--
--   Since $v\cdot u=\mathrm{id}_A$, each $x\in A$ lies on a strand of $\Gamma(v,u)$ from the left port $x$ to the right port $x$. The theorem says: if this strand avoids the interface points in $J$, then inserting any middle diagram that is the identity outside $J$ keeps $x$ fixed. The marked set does not depend on $a$, so a single support bound holds for all such middle diagrams at once, including their products and powers. Together with the separate bound $|\mathrm{mk}(v,u,J)|\le|J|$, this is the common support estimate used for corner reductions in the rank-loss argument.
--
--   **Formalization Note** Diagrams are `Pairing (A ⊕ B)`, composition is `compose`, $\Gamma(v,u)$ is `glueGraph v u`, and the outer ports are embedded by `outer`. The support is `support`, and the marked set is `marked v u J`, a `Finset A` defined with classical decidability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Automata/Diagram.lean#L62-L116

import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram

open OAI OAI.OneWayLiveness OAI.OneWayLiveness.Pairing
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

theorem OAI.OneWayLiveness.Pairing.support_sandwich_subset_marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) (a : Pairing (B ⊕ B))
    (ha : support a ⊆ J) : support (compose (compose v a) u) ⊆ marked v u J := by sorry
