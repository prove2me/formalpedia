-- Prove2me | Theorems.Thm_Kyprianou_Ch04_cor412_capped_renewal_factor
-- name    : Kyprianou.Ch04.cor412_capped_renewal_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:20:16.758856+00:00
-- url     : https://prove2.me/theorems/06656c7b-103e-591b-b2f9-9d5f02cb6e2a
-- title:
--   Strong Markov factorisation of the capped passage-position weight and future infimum reward
-- statement:
--   Strong Markov factorisation of the capped passage-position weight and future infimum reward.
-- source:
--   Kyprianou (2006), Chapter 4, Corollary 4.12.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Theorems.Thm_Kyprianou_Ch04_cor412_lower_stop
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_clock
import Theorems.Thm_Kyprianou_Ch04_cor412_capped_history_weight
import Theorems.Thm_Kyprianou_Ch04_cor412_rightcont_weight_factor
import Theorems.Thm_Kyprianou_Ch04_cor412_dyadic_reward_meas
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Strong Markov factorisation of the capped passage-position weight and future infimum reward. -/

theorem Kyprianou.Ch04.cor412_capped_renewal_factor
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ} (L : SpectrallyNegativeLevy P F)
    (n : NNReal) (T : Ω → NNReal)
    (hT : ∀ w, (T w : WithTop NNReal) =
      min (Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w) (n : WithTop NNReal))
    (β : ℝ) :
    let A : Set Ω := {w | Kyprianou.Ch03.firstHittingTime L.X (Iio 0) w ≤ (n : WithTop NNReal)}
    let W : Ω → ℝ≥0∞ := A.indicator (fun w => ENNReal.ofReal (Real.exp (β * L.X (T w) w)))
    let R : (NNReal → ℝ) → ℝ≥0∞ := fun f =>
      ⨅ q : ℕ × ℕ, ENNReal.ofReal (Real.exp (β * f ((q.1 : NNReal) / 2 ^ q.2)))
    (∫⁻ w, W w * R (fun t => L.X (T w + t) w - L.X (T w) w) ∂P) =
      (∫⁻ w, W w ∂P) * (∫⁻ w, R (fun t => L.X t w) ∂P) := by sorry
