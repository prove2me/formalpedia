-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_scalar_localization
-- name    : OAI.LipschitzCounterexample.LocalizedLinearization.scalar_localization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:50:20.094027+00:00
-- url     : https://prove2.me/theorems/4e760102-b47d-4b10-a691-c1d345cc73c7
-- title:
--   Weakly null free-space sequences vanish on asymptotically flat tests
-- statement:
--   For a pointed metric space $M$, $\mathcal F(M)$ is its Lipschitz-free space and $\langle\mu,f\rangle$ denotes the pairing of $\mu\in\mathcal F(M)$ with a Lipschitz function $f$ normalized by $f(0)=0$. $\mathcal F(M)$ has compact reduction if every weakly null sequence can be uniformly approximated, to any accuracy, by elements supported on one compact set containing $0$. Assume $\mathcal F(M)$ has compact reduction and $\mu_i$ is weakly null. Let $d_i$ be uniformly $L$-Lipschitz with $d_i(x)\to0$ pointwise. Suppose that for every $\eta>0$ there is a finite set $Z$ such that every $p\notin Z$ has an open neighbourhood on which $d_i$ is eventually $\eta$-Lipschitz. Then
--   $$
--   \bigl\langle\mu_i,\ d_i-d_i(0)\bigr\rangle\to0 .
--   $$
--
--   Here the pairing is with the normalized function $d_i-d_i(0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CompactLocalization.lean#L235-L310

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

open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
universe uM uI
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set
open Filter Set Topology LocalLipschitz
open scoped NNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem OAI.LipschitzCounterexample.LocalizedLinearization.scalar_localization (hcompact : FreeSpace.HasCompactReduction (M := M))
    {μ : ℕ → FreeSpace.Space M} (hw : WeakSequences.WeakNull μ)
    (d : ℕ → M → ℝ) {L : ℝ≥0} (hd : ∀ i, LipschitzWith L (d i))
    (hpoint : ∀ x, Tendsto (fun i => d i x) atTop (𝓝 0))
    (hgood : ∀ η : ℝ≥0, 0 < η → ∃ Z : Set M, Z.Finite ∧
      ∀ p, p ∉ Z → ∃ O : Set M, IsOpen O ∧ p ∈ O ∧
        ∀ᶠ i in atTop, LipschitzOnWith η (d i) O) :
    Tendsto (fun i => test (normalized (d i) (hd i)) (μ i)) atTop (𝓝 0) := by sorry
