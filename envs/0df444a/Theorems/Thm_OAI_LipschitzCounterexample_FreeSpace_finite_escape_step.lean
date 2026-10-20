-- Prove2me | Theorems.Thm_OAI_LipschitzCounterexample_FreeSpace_finite_escape_step
-- name    : OAI.LipschitzCounterexample.FreeSpace.finite_escape_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:58:35.57166+00:00
-- url     : https://prove2.me/theorems/60284a63-1cc2-43c5-ad22-f25eb24fda84
-- title:
--   An element escaping finite neighbourhoods yields a localized test
-- statement:
--   Let $M$ be a pointed metric space with Lipschitz-free space $\mathcal F(M)$; $\mathcal F_K(M)$ is the closed span of $\{\delta_x:x\in K\}$, and $\langle\mu,f\rangle$ is the pairing with a Lipschitz $f$ normalized by $f(0)=0$. An element $\mu$ is $\varepsilon$-approximable on $K$ if $\|\mu-\nu\|<\varepsilon$ for some $\nu\in\mathcal F_K(M)$. Let all $\mu_i$ be supported in $\bar B(0,R)$, let $\delta>0$, and suppose that for every finite $A\ni0$ some $\mu_i$ is not $\varepsilon$-approximable on the closed $\delta$-neighbourhood of $A$. Then for every $p$ and finite $A$ there are $i>p$, a finite $B\ni0$ and a Lipschitz $g$ with constant $3+\frac2\delta(2R+2)$ and $g(0)=0$ such that:
--   - $g=0$ on the $\delta$-neighbourhood of $A$;
--   - $g$ is supported in the $\delta$-neighbourhood of $B$;
--   $$
--   |\langle\mu_i,g\rangle|>\varepsilon/2 .
--   $$
--
--   Iterating this step produces equi-Lipschitz tests with pairwise disjoint supports.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/FiniteReduction.lean#L60-L138

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

theorem OAI.LipschitzCounterexample.FreeSpace.finite_escape_step {μ : ℕ → Space M} {ε : ℝ} (hε : 0 < ε)
    {R : ℝ≥0} (hsupp : ∀ i, μ i ∈ supported (Metric.closedBall 0 (R : ℝ)))
    {δ : ℝ≥0} (hδ : 0 < δ)
    (hfail : ∀ A : Finset M, (0 : M) ∈ A → ∃ i, ¬ Approximable (μ i) (Near A δ) ε)
    (p : ℕ) (A : Finset M) : ∃ i : ℕ, ∃ B : Finset M, ∃ g : M → ℝ,
      p < i ∧ (0 : M) ∈ B ∧
      LipschitzWith (3+(2/δ)*(2*R+2)) g ∧ g 0 = 0 ∧
      (∀ x ∈ Near A δ, g x = 0) ∧ (∀ x, g x ≠ 0 → x ∈ Near B δ) ∧
      ∀ hg : LipschitzWith (3+(2/δ)*(2*R+2)) g, ε/2 < |test (normalized g hg) (μ i)| := by sorry
