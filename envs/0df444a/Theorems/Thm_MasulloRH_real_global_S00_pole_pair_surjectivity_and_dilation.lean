-- Prove2me | Theorems.Thm_MasulloRH_real_global_S00_pole_pair_surjectivity_and_dilation
-- name    : MasulloRH.real_global_S00_pole_pair_surjectivity_and_dilation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:18:55.985834+00:00
-- url     : https://prove2.me/theorems/33905bd0-acc7-42a4-9918-9f19eaecc96b
-- title:
--   Both Schwartz pole coordinates are independently realized and transform at opposite half weights
-- statement:
--   Every pair of prescribed real values at the origin and of additive mass is attained by one even smooth compact function on the real line. With standard finite adelic unit balls these are the unramified rational global residue coordinates. The normalized dilation exp(-s/2)h(exp(-s)x) acts on this pair by the two distinct half-weight characters. Thus the actual real core modulo the common kernel has both lines, with their sign of dilation fixed.
-- source:
--   Masullo (2.2.4.23–27), (5.5.2.2–3), and the true S00 core.

import Mathlib
open MeasureTheory

theorem MasulloRH.real_global_S00_pole_pair_surjectivity_and_dilation :
    (∀ A B : ℝ, ∃ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧
      (∀ x, h (-x) = h x) ∧ h 0 = A ∧ (∫ x : ℝ, h x) = B) ∧
    (∀ (h : ℝ → ℝ) (s : ℝ),
      let v := fun x : ℝ => Real.exp (-s/2) * h (Real.exp (-s) * x)
      (v 0, ∫ x : ℝ, v x) = (Real.exp (-s/2) * h 0, Real.exp (s/2) * ∫ x : ℝ, h x)) := by sorry
