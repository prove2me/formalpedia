-- Prove2me | Theorems.Thm_Freiman_other22_geometry_base
-- name    : Freiman.other22_geometry_base
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:16.679933+00:00
-- url     : https://prove2.me/theorems/564f6cd2-6413-4739-ac85-1bf776fae7f0
-- title:
--   other22 geometry base
-- statement:
--   Translate Z normalization, positivity, the two large tests and necessary goodness to the initial source bounds.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_base (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryBaseEvent Z (other22Paths k) := by
  sorry
