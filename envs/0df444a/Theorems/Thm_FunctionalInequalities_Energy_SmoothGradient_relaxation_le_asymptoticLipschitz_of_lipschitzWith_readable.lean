-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_le_asymptoticLipschitz_of_lipschitzWith_readable
-- name    : FunctionalInequalities.Energy.SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:53.058107+00:00
-- url     : https://prove2.me/theorems/0c999886-ba48-46f7-9658-d121570cc5c9
-- title:
--   Smooth Relaxation Bound by Asymptotic-Lipschitz Energy
-- statement:
--   This statement formalizes the smooth-recovery inequality for a globally Lipschitz test.
--
--   Let $V$ be a finite-dimensional real inner-product space with complete Borel measurable and second-countable structure. Let $\nu$ be a probability measure on $V$, let $g:V\to\mathbb R$, and let $K\in[0,\infty)$. Assume:
--
--   1. $g$ is globally $K$-Lipschitz, expressed by `LipschitzWith K g`.
--   2. $g$ belongs to $L^2(\nu)$, expressed by `MemLp g 2 (\nu : Measure V)`.
--
--   Then the smooth-gradient relaxation of the $L^2(\nu)$ class of $g$ is bounded above by its asymptotic-Lipschitz energy:
--
--   $$
--   \operatorname{relaxation}(\nu)([g]_{L^2(\nu)})
--   \leq
--   \operatorname{AsymptoticLipschitz.energy}(\nu,g).
--   $$
--
--   Both sides are extended-valued energies in $[0,\infty]$. This is a reusable smooth-recovery estimate for globally Lipschitz functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.SmoothGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem relaxation_le_asymptoticLipschitz_of_lipschitzWith (ν : ProbabilityMeasure V)
--       {g : V → ℝ} {K : ℝ≥0} (hlip : LipschitzWith K g) (hmem : MemLp g 2 (ν : Measure V)) :
--       relaxation ν (hmem.toLp g) ≤ AsymptoticLipschitz.energy ν g
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/LocalSlope/Relaxation`](https://prove2.me/theorems/5763c613-ee60-472a-abfb-a2d2d79c15c8), [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd).
--
--   Supporting theorems: [`limsup_enorm_gradient_mollify_le`](https://prove2.me/theorems/b7115fba-b7b4-4e77-ad68-d8e10c4a65ff).
--
--   Previous: [`limsup_enorm_gradient_mollify_le`](https://prove2.me/theorems/b7115fba-b7b4-4e77-ad68-d8e10c4a65ff).
--
--   [Source excerpt, lines 559–561](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L559-L561) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L555-L653 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith_readable (ν : ProbabilityMeasure V)
    {g : V → ℝ} {K : ℝ≥0} (hlip : LipschitzWith K g) (hmem : MemLp g 2 (ν : Measure V)) :
    relaxation ν (hmem.toLp g) ≤ AsymptoticLipschitz.energy ν g := by sorry
