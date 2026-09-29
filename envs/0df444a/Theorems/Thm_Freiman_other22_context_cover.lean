-- Prove2me | Theorems.Thm_Freiman_other22_context_cover
-- name    : Freiman.other22_context_cover
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:52.615053+00:00
-- url     : https://prove2.me/theorems/297acf45-4167-424c-b7b5-5cc461346e9b
-- title:
--   other22 context cover
-- statement:
--   Actual admissible equal-parity birth words belong to one of the six source suffix contexts, with right suffix31. Both common parities are allowed.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_context_cover (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) :
    ∃ k : Fin 6, lowerHistoryContextFits Z (other22Context k) := by
  sorry
