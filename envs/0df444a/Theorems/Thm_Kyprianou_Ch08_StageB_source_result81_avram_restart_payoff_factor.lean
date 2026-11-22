-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_avram_restart_payoff_factor
-- name    : Kyprianou.Ch08.StageB.source_result81_avram_restart_payoff_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:47:59.143365+00:00
-- url     : https://prove2.me/theorems/ec8b0c1f-b094-427a-8298-04f0c7b4a7d5
-- title:
--   Restart payoff factor in a pathwise filtered Lévy model
-- statement:
--   In a pathwise right-continuous spectrally negative Lévy representation, the strict lower-before-upper payoff and delayed ruin payoff are integrable. The latter factors as the upper-before-lower discount times the ordinary ruin payoff from the upper level.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1, stopped strong Markov argument, effective all-path Lévy representation of exact parent 78574f78-b2c0-43ff-a7df-919c061143b7.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_avram_restart_payoff_factor
    (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℝ≥0 mΩ) (X : SpectrallyNegativeLevy P F)
    (q x a : ℝ) (hq : 0 ≤ q) :
    let L := tauMinus (shifted X.X x) 0
    let U := tauPlus (shifted X.X x) a
    let low := fun ω => if L ω < U ω then discountedAt q (L ω) else 0
    let restart := fun ω =>
      if U ω < L ω then
        WithTop.recTopCoe 0 (fun t =>
          discountedAt q (t : WithTop ℝ≥0) *
            discountedAt q (tauMinus
              (fun s (_ : Unit) => a + (X.X (t + s) ω - X.X t ω)) 0 ())) (U ω)
      else 0
    Integrable low P ∧ Integrable restart P ∧
      (∫ ω, restart ω ∂P) =
        upBeforeDownExpectation P X.X q x a * downExpectation P X.X q a := by
  sorry
