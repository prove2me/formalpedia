-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:42.52902+00:00
-- url     : https://prove2.me/theorems/80f4b23b-124c-49c3-a604-c5a3355c1bc0
-- title:
--   Smooth-Test and Local-Slope Poincaré Equivalence
-- statement:
--   This is an equivalence between two Poincaré test classes.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with Borel and second-countable structure. Let $\nu$ be a probability measure and $m$ an additive Haar measure, and assume $\nu\ll m$. For every finite nonnegative constant $C\in\mathbb{NNReal}$,
--
--   $$\mathrm{SmoothTest.Holds}(\nu,C)
--   \iff \mathrm{LocalSlope.Holds}(\nu,C).$$
--
--   The two predicates use their respective Lean-defined finite-energy test domains. The result is an exact equivalence, not merely a comparison of optimal constants; it imposes no log-concavity or moment hypothesis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem holds_iff_localSlope (ν : ProbabilityMeasure E) (m : Measure E)
--       [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) (C : NNReal) :
--       Holds (ν : Measure E) (C : ℝ) ↔ Poincare.LocalSlope.Holds ν C
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/LocalSlope/SmoothTestComparison`](https://prove2.me/theorems/1ad07877-0369-4792-9877-1dd2997c7c22).
--
--   Definition modules: [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1), [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Supporting theorems: [`admissible_iff_memLp_gradient`](https://prove2.me/theorems/284b0183-bfda-452b-b5ff-2efd469c4a7d), [`apply_eq_norm_gradient`](https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc).
--
--   [Source excerpt, lines 71–73](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LocalSlope/SmoothTestComparison.lean#L71-L73) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/LocalSlope/SmoothTestComparison.lean#L69-L118 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.LocalSlope.SmoothTestComparison`, declaration `FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LocalSlope_SmoothTestComparison

open MeasureTheory Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable (ν : ProbabilityMeasure E) (m : Measure E)
    [Measure.IsAddHaarMeasure m] (hν : (ν : Measure E) ≪ m) (C : NNReal) :
    Holds (ν : Measure E) (C : ℝ) ↔ Poincare.LocalSlope.Holds ν C := by sorry
