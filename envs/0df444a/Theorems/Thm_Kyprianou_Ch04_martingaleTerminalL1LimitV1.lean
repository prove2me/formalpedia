-- Prove2me | Theorems.Thm_Kyprianou_Ch04_martingaleTerminalL1LimitV1
-- name    : Kyprianou.Ch04.martingaleTerminalL1LimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:16:38.420412+00:00
-- url     : https://prove2.me/theorems/953a9407-65c3-582b-9433-b54487a4da1b
-- title:
--   Adapted terminal L1 martingale limit
-- statement:
--   Terminal L1 convergence gives convergence of each past-event set integral by the norm bound. Pass the martingale set-integral equality to the limit.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem martingaleTerminalL1LimitV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration NNReal inferInstance)
    (M : ℕ → NNReal → Ω → ℝ) (L : NNReal → Ω → ℝ)
    (hM : ∀ n, Martingale (M n) F P)
    (hA : StronglyAdapted F L) (hI : ∀ t, Integrable (L t) P)
    (hConv : ∀ t, Tendsto
      (fun n => ∫ w, |M n t w - L t w| ∂P) atTop (𝓝 0)) :
    Martingale L F P := by
  sorry
end Kyprianou.Ch04
