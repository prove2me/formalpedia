-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezed_phase_first_moment
-- name    : LogLogJam.Supplement.squeezed_phase_first_moment
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:28:20.390942+00:00
-- url     : https://prove2.me/theorems/6b0a6252-01db-447b-bff3-f49b721787ed
-- title:
--   The first circular moment of the squeezed phase density
-- statement:
--   The complex first moment of the phase density centered at α points along exp(iα). Its magnitude is at least q/2 times the zeroth moment, uniformly in 0 ≤ q < 1.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3; Lemma 8.24.

import Mathlib

namespace LogLogJam.Supplement

theorem squeezed_phase_first_moment (q α : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    let A := fun t : ℝ => ∑' n : ℕ,
      (((Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n)*q^n:ℝ):ℂ) *
        Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
    let p := fun x : ℝ => Real.sqrt (1-q^2)/(2*Real.pi) * ‖A (x-α)‖^2
    ∃ R : ℝ, q / 2 * (∫ x in Set.Ico 0 (2*Real.pi), p x) ≤ R ∧
      (∫ x in Set.Ico 0 (2*Real.pi), Complex.exp ((x:ℂ)*Complex.I) * (p x:ℂ)) =
        Complex.exp ((α:ℂ)*Complex.I)*(R:ℂ) := by sorry

end LogLogJam.Supplement
