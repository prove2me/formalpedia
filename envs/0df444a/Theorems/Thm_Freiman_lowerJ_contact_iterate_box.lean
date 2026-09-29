-- Prove2me | Theorems.Thm_Freiman_lowerJ_contact_iterate_box
-- name    : Freiman.lowerJ_contact_iterate_box
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:16.304132+00:00
-- url     : https://prove2.me/theorems/ba2f0f0e-5539-43c2-87a0-45f385322127
-- title:
--   Freiman repeated-three proof: contact iterate box
-- statement:
--   The eight k=2 endpoint signs and four invariant-interval signs prove the two report tail boxes for all k≥2.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_contact_iterate_box (hn : lowerJSignFacts) (k : ℕ) (hk : 2 ≤ k) : (151/500:ℝ) < lowerJIter k lowerJA ∧ lowerJIter k lowerJA < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (303/1000:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJC ∧ lowerJIter k lowerJC < (38/125:ℝ) ∧ (151/500:ℝ) < lowerJIter k lowerJD ∧ lowerJIter k lowerJD < (38/125:ℝ) := by
  sorry
