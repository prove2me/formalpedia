-- Prove2me | Theorems.Thm_Freiman_other22_geometry_normalizations
-- name    : Freiman.other22_geometry_normalizations
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:35:01.429849+00:00
-- url     : https://prove2.me/theorems/8a7201c7-a836-4635-959c-c6f1073fa9d2
-- title:
--   other22 geometry normalizations
-- statement:
--   The actual B retains first side, the20 step reflects strictly to R, and S retains the reflected incoming side; convert these full-width facts to source normalization events.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_normalizations (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryNormalizationEvents Z (other22Paths k) := by
  sorry
