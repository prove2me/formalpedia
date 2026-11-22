-- Prove2me | Theorems.Thm_MasulloRH_rapid_packet_translate_orthogonality_with_L2_differences
-- name    : MasulloRH.rapid_packet_translate_orthogonality_with_L2_differences
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:25:50.865179+00:00
-- url     : https://prove2.me/theorems/3064777b-6aa8-4d2e-a191-e3685f5f985e
-- title:
--   Orthogonality to rapid packet translates forces constancy for profiles with square-integrable differences
-- statement:
--   A bounded continuous profile with all finite translation differences in $L²$ that annihilates all translates of a nonzero continuous packet having all exponential moments is constant.
-- source:
--   Masullo §§9.1,9.2 and 11.2; supporting harmonic-analysis lemma for weighted spectral Riesz vectors.

import Mathlib
open MeasureTheory

theorem MasulloRH.rapid_packet_translate_orthogonality_with_L2_differences (b u : ℝ → ℂ) (hb : Continuous b) (hbd : ∃ M : ℝ, ∀ x : ℝ, ‖b x‖ ≤ M) (hd : ∀ d : ℝ, MemLp (fun x => b (x+d) - b x) 2 volume) (hu : Continuous u) (hu0 : u ≠ 0) (hdec : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * |x|) * ‖u x‖)) (hpair : ∀ c : ℝ, (∫ x : ℝ, b x * (starRingEnd ℂ) (u (x-c))) = 0) : ∃ m : ℂ, ∀ x : ℝ, b x = m := by sorry
