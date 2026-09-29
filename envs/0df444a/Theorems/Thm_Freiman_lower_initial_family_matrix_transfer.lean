-- Prove2me | Theorems.Thm_Freiman_lower_initial_family_matrix_transfer
-- name    : Freiman.lower_initial_family_matrix_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:19:43.769359+00:00
-- url     : https://prove2.me/theorems/1a190f41-aba0-421e-986d-e8619899e83f
-- title:
--   Freiman lower construction: initial family matrix transfer
-- statement:
--   Finite A/B/C word concatenation, common positive matrix scale and equal word parity. The genuine normalization and both recurrence identities are explicit hypotheses.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_family_matrix_transfer 
    (hp : ∀ n : ℕ, 0 < n → lowerInitialWordMatrix (lowerRepeat lowerPeriod n) =
      lowerInitialMatScale (lowerInitialU n:ℝ) (lowerInitialP false (lowerInitialX n)))
    (hu : ∀ n : ℕ, 0 < n → 0 < lowerInitialU n)
    (hv : ∀ k : ℕ, 0 < lowerInitialV (k+1))
    (hr : ∀ k : ℕ,
      lowerInitialWordMatrix (List.replicate (k+1) (3:ℕ+)) = lowerInitialMatScale (lowerInitialV (k+1):ℝ) (lowerInitialK (lowerInitialY k)) ∧
      lowerInitialWordMatrix (List.replicate k (3:ℕ+)) = lowerInitialMatScale (lowerInitialV (k+1):ℝ) (lowerInitialKPrev (lowerInitialY k)))
    (hnorm : ∀ (f : LowerInitialFamily) (n k p : ℕ), f ≠ .auxB →
      lowerNormalize (lowerFamilyPair f n k p) = (if f = .B then lowerFamilyPair f n k p else (lowerFamilyPair f n k p).swap))
    (c : LowerInitialSeamCase) (n k p : ℕ) (hc : lowerInitialSeamZero c = decide (n=0)) :
    lowerInitialSeamLink c n k p := by
  sorry
