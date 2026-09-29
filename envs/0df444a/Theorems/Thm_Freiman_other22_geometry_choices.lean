-- Prove2me | Theorems.Thm_Freiman_other22_geometry_choices
-- name    : Freiman.other22_geometry_choices
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:32.13875+00:00
-- url     : https://prove2.me/theorems/b490b9a1-d833-41fa-86de-b09a8cda3d2d
-- title:
--   other22 geometry choices
-- statement:
--   The actual B source branch has exactly the two alternatives small-first or large-first/small-second; the following10 step adds no numerical choice condition.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_choices (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryChoiceEvents Z (other22Paths k) := by
  sorry
