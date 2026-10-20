-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_hasCompactReduction
-- name    : OAI.LipschitzCounterexample.FreeSpace.hasCompactReduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:03:41.928994+00:00
-- url     : https://prove2.me/theorems/9a9c2eee-5731-4607-8657-d3f8b3066e01
-- title:
--   Free spaces of complete metric spaces have compact reduction
-- statement:
--   Let $M$ be a pointed metric space with Lipschitz-free space $\mathcal F(M)$; $\mathcal F_K(M)$ is the closed span of $\{\delta_x:x\in K\}$, and $\langle\mu,f\rangle$ is the pairing with a Lipschitz $f$ normalized by $f(0)=0$. An element $\mu$ is $\varepsilon$-approximable on $K$ if $\|\mu-\nu\|<\varepsilon$ for some $\nu\in\mathcal F_K(M)$. If $M$ is complete, then $\mathcal F(M)$ has compact reduction: for every weakly null sequence $\mu_i$ and $\tau>0$ there is a compact $K\ni0$ with
--   $$
--   \forall i\ \exists\nu\in\mathcal F_K(M),\ \|\mu_i-\nu\|<\tau .
--   $$
--
--   So weakly null sequences in free spaces are uniformly almost compactly supported.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactReduction.lean#L116-L130

import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparatingCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlowAngles
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RotatingStages
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertBijection
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalOrthogonality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SeparableCoordinates
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_LocalLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLipschitz
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactLocalization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompleteContinuity
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SupportedDuality
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Multipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteReduction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteMultipliers
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactSupports
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CompactReduction

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem OAI.LipschitzCounterexample.FreeSpace.hasCompactReduction [CompleteSpace M] :
    ∀ μ : ℕ → Space M, WeakSequences.WeakNull μ → ∀ τ : ℝ, 0 < τ →
      ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
        ∀ i, ∃ ν : Space M, ν ∈ supported K ∧ ‖μ i-ν‖ < τ := by sorry
