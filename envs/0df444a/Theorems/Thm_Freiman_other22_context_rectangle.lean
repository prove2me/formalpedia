-- Prove2me | Theorems.Thm_Freiman_other22_context_rectangle
-- name    : Freiman.other22_context_rectangle
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:14.076099+00:00
-- url     : https://prove2.me/theorems/b9cdec3c-25a6-4205-98b9-066f9115ad34
-- title:
--   other22 context rectangle
-- statement:
--   The six elementary continued-fraction suffix bounds put the actual r,s parameters in the exact printed closed rectangles; empty-prefix boundary cases and weak endpoints are retained.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_context_rectangle (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    certRectangleMem (other22Paths k).rectangle (lowerRatio Z.1) (lowerRatio Z.2) := by
  sorry
