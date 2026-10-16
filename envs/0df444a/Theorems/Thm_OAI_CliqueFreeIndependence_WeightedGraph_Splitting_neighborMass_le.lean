-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_WeightedGraph_Splitting_neighborMass_le
-- name    : OAI.CliqueFreeIndependence.WeightedGraph.Splitting.neighborMass_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:35:05.960773+00:00
-- url     : https://prove2.me/theorems/cae51804-40f2-4904-be71-0e11df1646ff
-- title:
--   Neighborhood masses in the splitting graph are bounded by an admissibility constant
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, with adjacency $u\sim v$, and let $\vec E(G)$ be its finite set of oriented edges $e=(e^-,e^+)$, $e^-\sim e^+$, with reversal $\bar e=(e^+,e^-)$. Let $F:\vec E(G)\to\vec E(G)$ satisfy $F(e)^-=e^-$ for all $e$, let $\mathrm{good}$ be a predicate on $\vec E(G)$, and let $H$ be the splitting graph on the vertex set $\vec E(G)$, in which $a\sim_Hb$ if and only if some oriented edge $e$ satisfies $\mathrm{good}(e)$, $\mathrm{good}(\bar e)$, $F(e)=a$ and $F(\bar e)=b$. Given $w:V\to\mathbb R$, give the vertex $a$ of $H$ the weight $w_{a^-}$, and write $N_H(a)$ for the neighborhood of $a$ in $H$.
--
--   Let $K:\vec E(G)\times\vec E(G)\to\mathbb R$ be a stochastic kernel, i.e. $K(a,e)\ge0$ for all $a,e$ and $\sum_{e\in\vec E(G)}K(a,e)=1$ for every $a$, and let $L\ge0$ be such that the admissibility condition
--
--   $$
--   w_{e^+}\le L\,K\big(F(e),e\big)\qquad\text{for every oriented edge }e\text{ with }\mathrm{good}(e)
--   $$
--
--   holds. Then every vertex $a$ of $H$ has neighborhood mass at most $L$:
--
--   $$
--   \sum_{b\in N_H(a)}w_{b^-}\le L .
--   $$
--
--   Think of $K(a,\cdot)$ as a probability distribution on the oriented edges attached to the copy $a$. If the weight of the far endpoint of every good edge is dominated by $L$ times its probability under the kernel of the copy it is routed to, then each copy has weighted degree at most $L$ in the split graph. This is how vertex splitting restores a uniform bound on neighborhood masses.
--
--   **Formalization Note** The weight on $H$ is `w ∘ EdgeState.src` and the conclusion is `neighborMass (graph F hF good) (w ∘ EdgeState.src) a ≤ L`. No sign condition on $w$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Splitting.lean#L58-L90

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.WeightedGraph OAI.CliqueFreeIndependence.WeightedGraph.Splitting
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
variable {V : Type u} [Fintype V]
attribute [local instance 10000] edgeStateDecEq
variable {G : SimpleGraph V}

theorem OAI.CliqueFreeIndependence.WeightedGraph.Splitting.neighborMass_le (w : V → ℝ) (F : EdgeState G → EdgeState G)
    (hF : ∀ e, (F e).src = e.src) (good : EdgeState G → Prop)
    (K : EdgeState G → EdgeState G → ℝ) (hK0 : ∀ a e, 0 ≤ K a e)
    (hK1 : ∀ a, ∑ e, K a e = 1) {L : ℝ} (hL : 0 ≤ L)
    (hadm : ∀ e, good e → w e.dst ≤ L * K (F e) e) (a : EdgeState G) :
    neighborMass (graph F hF good) (w ∘ EdgeState.src) a ≤ L := by sorry
