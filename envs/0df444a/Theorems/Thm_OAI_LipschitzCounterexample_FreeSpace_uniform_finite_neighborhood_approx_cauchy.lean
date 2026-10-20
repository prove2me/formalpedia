-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_uniform_finite_neighborhood_approx_cauchy
-- name    : OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx_cauchy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T20:07:36.890464+00:00
-- url     : https://prove2.me/theorems/27c3f3ba-4b92-451e-9278-3820380f2bb6
-- title:
--   Bounded weakly Cauchy sequences concentrate near a finite set
-- statement:
--   Let $M$ be a pointed metric space with Lipschitz-free space $\mathcal F(M)$; $\mathcal F_K(M)$ is the closed span of $\{\delta_x:x\in K\}$, and $\langle\mu,f\rangle$ is the pairing with a Lipschitz $f$ normalized by $f(0)=0$. An element $\mu$ is $\varepsilon$-approximable on $K$ if $\|\mu-\nu\|<\varepsilon$ for some $\nu\in\mathcal F_K(M)$. Let $\mu_i$ be weakly Cauchy and supported in a fixed ball $\bar B(0,R)$. Then for all $\delta,\varepsilon>0$ there is a finite $A\ni0$ such that
--   $$
--   \mu_i\ \text{is }\varepsilon\text{-approximable on }\{x:\ d(x,A)\le\delta\}\quad\text{for all }i .
--   $$
--
--   This is the weakly Cauchy version of the finite-neighbourhood reduction.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/CauchyApproximation.lean#L68-L110

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

theorem OAI.LipschitzCounterexample.FreeSpace.uniform_finite_neighborhood_approx_cauchy {μ : ℕ → Space M}
    (hw : WeakSequences.WeakCauchy μ) {R : ℝ≥0}
    (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset M, (0 : M) ∈ A ∧ ∀ i, Approximable (μ i) (Near A δ) ε := by sorry
