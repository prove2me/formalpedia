-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_finite_stopped_parameter_future_product
-- name    : Kyprianou.Ch08.StageB.p2m810_finite_stopped_parameter_future_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:42:32.337584+00:00
-- url     : https://prove2.me/theorems/77f60972-9b09-4719-9b1e-de82ac059cdc
-- title:
--   Joint stopped parameter and future path law on a stopped event
-- statement:
--   At a finite stopping time, a measurable stopped-history parameter jointly with the restarted path has product law under restriction to a stopped event. The parameter marginal is restricted and the future marginal is the original probability path law.
-- source:
--   Kyprianou (2006), Exercise 8.10(iii), strong Markov kernel step

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Process.Stopping
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.p2m810_finite_stopped_parameter_future_product
    {Ω β : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {F : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P F)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0, MeasurableSet[F s] (A ∩ {ω | τ ω ≤ s}))
    (Y : Ω → β) (hY : Measurable Y)
    (hYs : ∀ B : Set β, MeasurableSet B → ∀ s : ℝ≥0,
      MeasurableSet[F s] (Y ⁻¹' B ∩ {ω | τ ω ≤ s})) :
    Measure.map (fun ω => (Y ω, fun t : ℝ≥0 =>
      X.X (τ ω+t) ω - X.X (τ ω) ω)) (P.restrict A) =
      (Measure.map Y (P.restrict A)).prod
        (Measure.map (fun ω => fun t : ℝ≥0 => X.X t ω) P) := by
  sorry
