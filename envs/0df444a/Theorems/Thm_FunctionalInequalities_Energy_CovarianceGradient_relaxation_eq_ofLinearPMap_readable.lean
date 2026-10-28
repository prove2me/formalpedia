-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_eq_ofLinearPMap_readable
-- name    : FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:25.118297+00:00
-- url     : https://prove2.me/theorems/ecd8db80-1079-4c3b-8976-dc3390ed944f
-- title:
--   Covariance Relaxation as a Weighted-Gradient Relaxation
-- statement:
--   This identifies the covariance relaxation with a sequential pre-energy relaxation.
--
--   Let $V$ be a finite-dimensional complete real inner-product space with its Borel measurable structure, let $\nu$ be a probability measure on $V$, let $m$ be an additive Haar measure, and let $B:V\to V$ be continuous linear. Assume:
--
--   1. $\nu$ is absolutely continuous with respect to $m$;
--   2. the frontier of the support of $\nu$ has $\nu$-measure zero;
--   3. for every $v\in V$,
--
--   $$
--   \langle\operatorname{Cov}(\nu)v,v\rangle=\|Bv\|^2.
--   $$
--
--   Then
--
--   $$
--   \operatorname{relaxation}(\nu)
--   =
--   \operatorname{sequentialRelaxation}\bigl(\operatorname{PreEnergy.ofLinearPMap}(\operatorname{WeightedGradient.operator}(\nu,B))\bigr).
--   $$
--
--   The result is the formal bridge between covariance energy and the squared-norm energy of a weighted gradient operator.
--
--   **Formalization Note** The equality is between extended nonnegative-valued functionals; the absolute-continuity and support-frontier hypotheses are explicit.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.CovarianceGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem relaxation_eq_ofLinearPMap (hac : (ν : Measure V) ≪ m)
--       (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
--       (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) :
--       relaxation ν =
--         (PreEnergy.ofLinearPMap (operator ν B hac)).sequentialRelaxation
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/WeightedGradient/Basic`](https://prove2.me/theorems/f6b93e94-4e8d-4cc9-94ea-458e2669b85c).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Energy/Relaxation/LinearPMap`](https://prove2.me/theorems/2ed50aac-81dd-45da-b8c8-597e80695a44), [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43), [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Supporting theorems: [`weightedTest_iff_exists_test`](https://prove2.me/theorems/6e254f19-783a-445b-a40f-180ee3e4ec09).
--
--   Previous: [`weightedTest_iff_exists_test`](https://prove2.me/theorems/6e254f19-783a-445b-a40f-180ee3e4ec09).
--
--   [Source excerpt, lines 349–353](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean#L349-L353) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean#L347-L384 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.WeightedGradient.Basic`, declaration `FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic

open MeasureTheory Filter Topology InnerProductSpace
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [MeasurableSpace V] (ν : MeasureTheory.ProbabilityMeasure V) (B : V →L[ℝ] V)
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
open FunctionalInequalities.Energy.WeightedGradient

theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_eq_ofLinearPMap_readable (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) :
    relaxation ν =
      (PreEnergy.ofLinearPMap (operator ν B hac)).sequentialRelaxation := by sorry
