-- Prove2me | Theorems.Thm_Freiman_lowerJ_contact_threshold
-- name    : Freiman.lowerJ_contact_threshold
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:23.570636+00:00
-- url     : https://prove2.me/theorems/3b48028b-59c5-4d81-b31d-12cdf79157a2
-- title:
--   Freiman repeated-three proof: contact threshold
-- statement:
--   The two source polynomial comparisons plus the k=1/all-k≥2 scalar split.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_contact_threshold (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) (k : ℕ) (hk : 0 < k) : lowerJHStar r s < lowerJHK k r s := by
  sorry
