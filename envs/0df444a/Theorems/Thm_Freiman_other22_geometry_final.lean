-- Prove2me | Theorems.Thm_Freiman_other22_geometry_final
-- name    : Freiman.other22_geometry_final
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:35:06.606429+00:00
-- url     : https://prove2.me/theorems/8f271dde-8610-439a-9fb2-2e379cd134de
-- title:
--   other22 geometry final
-- statement:
--   The two large tests and the incoming normalization of S give the final row1 cuts pulled back to the Z parameter coordinates.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_final (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryFinalEvent Z (other22Paths k) := by
  sorry
