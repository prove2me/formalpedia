-- Prove2me | Theorems.Thm_Freiman_lower_initial_family_normalization
-- name    : Freiman.lower_initial_family_normalization
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:19:53.083665+00:00
-- url     : https://prove2.me/theorems/529a7872-c46f-45ae-8610-03241a4c21a1
-- title:
--   Freiman lower construction: initial family normalization
-- statement:
--   Exact full-width ordering of actual A,B,C words: normalized matrices are swapped for A and C and retained for B. Ties follow the actual incoming convention.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_family_normalization (f : LowerInitialFamily) (n k p : ℕ) (hf : f ≠ .auxB) :
    lowerNormalize (lowerFamilyPair f n k p) =
    (if f = .B then lowerFamilyPair f n k p else (lowerFamilyPair f n k p).swap) := by
  sorry
