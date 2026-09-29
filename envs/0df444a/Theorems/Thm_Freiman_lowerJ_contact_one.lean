-- Prove2me | Theorems.Thm_Freiman_lowerJ_contact_one
-- name    : Freiman.lowerJ_contact_one
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:12.723236+00:00
-- url     : https://prove2.me/theorems/0129f09b-858d-4c49-86bb-a5d6bce82c00
-- title:
--   Freiman repeated-three proof: contact one
-- statement:
--   The k=1 symmetric-matrix contact factor reduces exactly to the report H1.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_contact_one (r s : ℝ) : lowerJHK 1 r s = lowerJH1 r s := by
  sorry
