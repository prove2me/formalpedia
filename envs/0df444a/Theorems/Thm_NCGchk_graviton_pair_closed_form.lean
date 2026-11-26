-- Prove2me | Theorems.Thm_NCGchk_graviton_pair_closed_form
-- name    : NCGchk.graviton_pair_closed_form
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T12:21:30.989535+00:00
-- url     : https://prove2.me/theorems/3ad0c1be-2c86-41e0-bb4a-9c98aefc0492
-- title:
--   Graviton pair closed form (check)
-- statement:
--   Graviton pair amplitude equals dilogarithm closed form.

import Mathlib

namespace NCGchk
noncomputable def dilog (z : ℂ) : ℂ := ∑' k : ℕ, z ^ (k + 1) / (k + 1 : ℂ) ^ 2
noncomputable def radialVar (s : ℝ) (k : ℕ) : ℝ := 1 / (2 * s * (k + 1))
noncomputable def pairTerm (s : ℝ) (k : ℕ) : ℂ :=
  2 * (radialVar s k : ℂ) ^ 2 * Complex.exp (-2 * Complex.I * (k + 1 : ℂ) / (s : ℂ))
noncomputable def pairAmplitude (s : ℝ) : ℂ := ∑' k : ℕ, pairTerm s k
end NCGchk

namespace NCGchk
theorem graviton_pair_closed_form (s : ℝ) (hs : 0 < s) :
    Summable (fun k : ℕ => ‖pairTerm s k‖) ∧
    pairAmplitude s = dilog (Complex.exp (-2 * Complex.I / (s : ℂ))) / (2 * (s : ℂ) ^ 2) := by sorry
end NCGchk
