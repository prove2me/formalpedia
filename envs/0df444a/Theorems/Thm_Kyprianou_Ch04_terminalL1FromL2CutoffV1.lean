-- Prove2me | Theorems.Thm_Kyprianou_Ch04_terminalL1FromL2CutoffV1
-- name    : Kyprianou.Ch04.terminalL1FromL2CutoffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:04:19.906947+00:00
-- url     : https://prove2.me/theorems/5f9d0176-2f0d-5100-be0e-82127b752b51
-- title:
--   Terminal L1 convergence from L2 convergence on a probability space
-- statement:
--   Terminal L1 convergence from L2 convergence on a probability space.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem terminalL1FromL2CutoffV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (M : Ω → ℝ)
    (hm : ∀ n, Measurable (Y n)) (hM : Measurable M)
    (hi : ∀ n, Integrable (fun w => (Y n w)^2) P)
    (hI : Integrable (fun w => (M w)^2) P)
    (h : Tendsto (fun n => ∫ w, (Y n w - M w)^2 ∂P) atTop (𝓝 0)) :
    Integrable M P ∧ Tendsto (fun n => ∫ w, |Y n w - M w| ∂P) atTop (𝓝 0) := by
  sorry
end Kyprianou.Ch04
