-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_weightedTest_iff_exists_test_readable
-- name    : FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:21.274399+00:00
-- url     : https://prove2.me/theorems/6e254f19-783a-445b-a40f-180ee3e4ec09
-- title:
--   Weighted Tests as Covariance-Gradient Tests
-- statement:
--   This characterizes weighted-gradient tests as covariance-gradient tests.
--
--   Let $V$ be a complete real inner-product space with its measurable structure, let $\nu$ be a probability measure on $V$, and let $B:V\to V$ be a continuous linear map. Assume that for every $v\in V$,
--
--   $$
--   \langle \operatorname{Cov}(\nu)v,v\rangle=\|Bv\|^2.
--   $$
--
--   Then for every function $g:V\to\mathbb R$,
--
--   $$
--   \operatorname{IsTest}(\nu,B,g)
--   \quad\Longleftrightarrow\quad
--   \exists f\in\operatorname{Test}(\nu),\ f=g.
--   $$
--
--   Here `IsTest ν B g` is the weighted-gradient test condition and `Test ν` is the covariance-gradient test class.
--
--   The equivalence transfers between the two test descriptions whenever the covariance quadratic form is represented by the squared norm of $B$.
--
--   **Formalization Note** No finite-dimensionality assumption is required by this declaration.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.CovarianceGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem weightedTest_iff_exists_test
--       (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
--       IsTest ν B g ↔ ∃ f : Test ν, f.toFun = g
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/WeightedGradient/Basic`](https://prove2.me/theorems/f6b93e94-4e8d-4cc9-94ea-458e2669b85c).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43).
--
--   Next: [`relaxation_eq_ofLinearPMap`](https://prove2.me/theorems/ecd8db80-1079-4c3b-8976-dc3390ed944f).
--
--   [Source excerpt, lines 310–312](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean#L310-L312) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean#L308-L323 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.WeightedGradient.Basic`, declaration `FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_WeightedGradient_Basic

open MeasureTheory Filter Topology InnerProductSpace
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable [MeasurableSpace V] (ν : MeasureTheory.ProbabilityMeasure V) (B : V →L[ℝ] V)
variable [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {m : MeasureTheory.Measure V} [m.IsAddHaarMeasure]
open FunctionalInequalities.Energy.WeightedGradient
omit [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.CovarianceGradient.weightedTest_iff_exists_test_readable
    (hB : ∀ v, inner ℝ (Covariance.operator (ν : Measure V) v) v = ‖B v‖ ^ 2) (g : V → ℝ) :
    IsTest ν B g ↔ ∃ f : Test ν, f.toFun = g := by sorry
