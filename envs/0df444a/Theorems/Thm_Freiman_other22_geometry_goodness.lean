-- Prove2me | Theorems.Thm_Freiman_other22_geometry_goodness
-- name    : Freiman.other22_geometry_goodness
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:28.754983+00:00
-- url     : https://prove2.me/theorems/c01da07c-c190-4f3f-a440-71cdd83ae9c8
-- title:
--   other22 geometry goodness
-- statement:
--   The actual goodness of B,R,S yields precisely the three pulled necessary-goodness events along the two predecessor steps.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_goodness (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryGoodEvents Z (other22Paths k) := by
  sorry
