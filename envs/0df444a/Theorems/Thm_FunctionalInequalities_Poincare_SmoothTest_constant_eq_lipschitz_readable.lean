-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_constant_eq_lipschitz_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:53.511475+00:00
-- url     : https://prove2.me/theorems/ad3e672a-6889-4720-aee1-47c1405b013e
-- title:
--   Smooth-Test Constant Equals Lipschitz-Gradient Constant
-- statement:
--   This identifies two optimal Poincaré constants.
--
--   Let $V$ be a finite-dimensional real inner-product normed space with Borel and second-countable structure. Let $\nu$ be a probability measure, $m$ an additive Haar measure, and assume $\nu\ll m$ and
--   $$\nu\bigl(\partial\operatorname{supp}\nu\bigr)=0.$$
--   Then the smooth-test constant equals the optimal constant of the Lipschitz-gradient relaxation:
--
--   $$\mathrm{SmoothTest.constant}(\nu)
--   =\mathrm{L2Energy.constant}\bigl(\nu,\mathrm{LipschitzGradient.relaxation}(\nu,m,\nu\ll m)\bigr).$$
--
--   This is an equality of optimal values, which may be $\infty$; it does not assert that either constant is finite.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem constant_eq_lipschitz
--       (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
--       constant (ν : Measure V) =
--         Poincare.L2Energy.constant ν (Energy.LipschitzGradient.relaxation ν m hac)
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/LipschitzGradient/Comparison`](https://prove2.me/theorems/2c2b9cea-02c3-4658-a545-11edfb033e0d).
--
--   Definition modules: [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f), [`Poincare/L2/Energy`](https://prove2.me/theorems/2c373d63-eba6-4063-92d2-2450951b5927).
--
--   Supporting theorems: [`holds_ofPreEnergy_of_localSlope`](https://prove2.me/theorems/d102feac-ee7b-49ef-9880-953e2bd04ed9), [`localSlope_holds_of_relaxation`](https://prove2.me/theorems/b98a1acd-890f-4c84-8b2d-782bb9d924ba), [`holds_iff_localSlope`](https://prove2.me/theorems/80f4b23b-124c-49c3-a604-c5a3355c1bc0), [`holds_ofPreEnergy_iff`](https://prove2.me/theorems/45fe7f2a-781b-4639-a2c2-4c48911bc95c).
--
--   Previous: [`localSlope_holds_of_relaxation`](https://prove2.me/theorems/b98a1acd-890f-4c84-8b2d-782bb9d924ba) · Next: [`relaxation_le_mul_lipschitz`](https://prove2.me/theorems/62ed0b65-a0a8-46f7-b7c9-4f855a09ceaf).
--
--   [Source excerpt, lines 174–177](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L174-L177) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/LipschitzGradient/Comparison.lean#L172-L194 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.LipschitzGradient.Comparison`, declaration `FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_LipschitzGradient_Comparison

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable (ν : MeasureTheory.ProbabilityMeasure V) (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Poincare.SmoothTest.constant_eq_lipschitz_readable
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    constant (ν : Measure V) =
      Poincare.L2Energy.constant ν (Energy.LipschitzGradient.relaxation ν m hac) := by sorry
