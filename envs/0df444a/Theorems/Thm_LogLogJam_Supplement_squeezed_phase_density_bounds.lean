-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezed_phase_density_bounds
-- name    : LogLogJam.Supplement.squeezed_phase_density_bounds
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T19:26:26.581562+00:00
-- url     : https://prove2.me/theorems/c3a9a35b-0a95-40db-843d-85798e58be68
-- title:
--   Peak and antipodal estimates for the squeezed phase density
-- statement:
--   For 0 ≤ q < 1, the phase density is at least 1/(32π(1−q)) within distance (1−q)/2 of its peak. It is at most 2√(1−q²)/π throughout the opposite semicircle.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3; Lemmas 8.20–8.22 and 8.25.

import Mathlib

namespace LogLogJam.Supplement

theorem squeezed_phase_density_bounds (q : ℝ) (hq : 0 ≤ q) (hq' : q < 1) :
    let A := fun t : ℝ => ∑' n : ℕ,
      (((Real.sqrt (Nat.centralBinom n) / (2:ℝ)^n)*q^n:ℝ):ℂ) *
        Complex.exp (Complex.I*((-((n:ℝ)*t)):ℝ))
    let p := fun t : ℝ => Real.sqrt (1-q^2)/(2*Real.pi) * ‖A t‖^2
    (∀ t : ℝ, |t| ≤ (1-q)/2 → 1/(32*Real.pi) ≤ (1-q)*p t) ∧
    (∀ t : ℝ, Real.cos t ≤ 0 → p t ≤ 2*Real.sqrt (1-q^2)/Real.pi) := by sorry

end LogLogJam.Supplement
