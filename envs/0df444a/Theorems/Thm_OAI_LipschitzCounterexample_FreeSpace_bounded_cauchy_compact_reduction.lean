-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_bounded_cauchy_compact_reduction
-- name    : OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_compact_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:09:06.775596+00:00
-- url     : https://prove2.me/theorems/eb5e3de5-d18d-453d-ac3f-12bc6cf17f44
-- title:
--   Bounded weakly Cauchy free-space sequences reduce to a compact support
-- statement:
--   Let $M$ be a pointed metric space with Lipschitz-free space $\mathcal F(M)$, and let $\mathcal F_K(M)$ be the closed span of $\{\delta_x:x\in K\}$. Let $M$ be complete and $\mu_i$ weakly Cauchy with all $\mu_i$ supported in $\bar B(0,R)$. Then for every $\tau>0$ there are a compact $K\ni0$ and a weakly Cauchy sequence $\nu_i$ in $\mathcal F_K(M)$ with
--   $$
--   \|\mu_i-\nu_i\|<\tau\quad\text{for all }i .
--   $$
--
--   This is the weakly Cauchy analogue of the compact reduction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CauchyReduction.lean#L60-L128

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
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_CauchyReduction

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.FreeSpace
universe uM uE
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open scoped NNReal Topology
open Filter Set LocalizedLinearization
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem OAI.LipschitzCounterexample.FreeSpace.bounded_cauchy_compact_reduction [CompleteSpace M] {R : ℝ≥0} {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ)
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {τ : ℝ} (hτ : 0 < τ) : ∃ K : Set M, IsCompact K ∧ (0 : M) ∈ K ∧
      ∃ ν : ℕ → Space M, WeakSequences.WeakCauchy ν ∧
        (∀ i, ν i ∈ supported K) ∧ ∀ i, ‖μ i-ν i‖ < τ := by sorry
