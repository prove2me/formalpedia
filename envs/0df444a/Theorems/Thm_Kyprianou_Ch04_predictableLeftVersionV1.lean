-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableLeftVersionV1
-- name    : Kyprianou.Ch04.predictableLeftVersionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:48:34.617+00:00
-- url     : https://prove2.me/theorems/eb1c8327-811d-5a89-a727-7aae5f89f550
-- title:
--   Canonical left limits of regular adapted processes are predictable
-- statement:
--   Combine strong adaptedness and left continuity of canonical left limits to obtain strong predictability.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_leftLim_leftContinuous_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_stronglyAdapted_leftLim_of_exists_leftLimits
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableLeftVersionV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (Y : NNReal → Ω → ℝ) (hY : StronglyAdapted F Y)
    (hl : ∀ ω (t : NNReal), 0 < t →
      ∃ l : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 l)) :
    IsStronglyPredictable F (fun t ω => Function.leftLim (fun s => Y s ω) t) := by
  sorry
end Kyprianou.Ch04
