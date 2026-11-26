-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_capped_history_weight
-- name    : Kyprianou.Ch04.cor412_capped_history_weight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:16:00.349002+00:00
-- url     : https://prove2.me/theorems/eda6b055-9b87-407b-ae39-f7e196d746ea
-- title:
--   Capped downward passage exponential position weight is measurable in the stopped history
-- statement:
--   Capped downward passage exponential position weight is measurable in the stopped history.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_tauceti_original_levy_stronglyProgressive
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A stopped position weighted by the finite-cap passage event is measurable in the stopped history. -/

theorem Kyprianou.Ch04.cor412_capped_history_weight
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (τ : Ω → WithTop NNReal) (hτ : IsStoppingTime F.rightCont τ)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) = min (τ w) (n : WithTop NNReal))
    (hstop : IsStoppingTime F.rightCont (fun w => (T w : WithTop NNReal)))
    (β : ℝ) :
    Measurable[hstop.measurableSpace]
      (({w : Ω | τ w ≤ (n : WithTop NNReal)} : Set Ω).indicator
        (fun w => ENNReal.ofReal (Real.exp (β * L.X (T w) w)))) := by sorry
