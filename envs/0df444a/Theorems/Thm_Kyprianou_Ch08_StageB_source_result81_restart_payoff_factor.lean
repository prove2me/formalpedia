-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_restart_payoff_factor
-- name    : Kyprianou.Ch08.StageB.source_result81_restart_payoff_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T13:13:43.716048+00:00
-- url     : https://prove2.me/theorems/78574f78-b2c0-43ff-a7df-919c061143b7
-- title:
--   Strong Markov factor for restarted ruin
-- statement:
--   Apply the strong Markov property to the future increment path on upper-first paths. The past weight is the discounted upper crossing payoff, and the future reward is the discounted lower crossing of the new path from a. Measurability follows by expressing strict crossings through rational-time coordinates on càdlàg paths, and the integrands are bounded for nonnegative discount.
-- source:
--   Kyprianou (2006), Chapter 8, proof of (8.9), p. 215. Decomposition of 3c242566-b9e1-49b0-bbd8-ab10f9c26428.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open MeasureTheory Filter Set Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_restart_payoff_factor
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : SpectrallyNegativeModel Ω P)
    (q x a : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hxa : x ≤ a) :
    let L := tauMinus (shifted D.X x) 0
    let U := tauPlus (shifted D.X x) a
    let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0
    let restart := fun ω =>
      if U ω < L ω then
        WithTop.recTopCoe 0 (fun t =>
          discountedAt q (t : WithTop ℝ≥0) *
            discountedAt q (tauMinus
              (fun s (_ : Unit) => a + (D.X (t + s) ω - D.X t ω)) 0 ())) (U ω)
      else 0
    Integrable low P ∧ Integrable restart P ∧
      (∫ ω, restart ω ∂P) =
        upBeforeDownExpectation P D.X q x a * downExpectation P D.X q a := by
  sorry
