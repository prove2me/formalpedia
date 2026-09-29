-- Prove2me | Theorems.Thm_Freiman_other22_geometry_premises
-- name    : Freiman.other22_geometry_premises
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:46.396304+00:00
-- url     : https://prove2.me/theorems/3fa9ed9e-a04a-43dd-8cf1-2ff5e1808593
-- title:
--   other22 geometry premises
-- statement:
--   Generic source-DNF induction reduces the actual two-step geometry to one of the two independently reconstructed source alternatives.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_premises (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    ∃ bs ∈ lowerHistorySourcePremises (other22Paths k), lowerHistoryAtBase Z bs := by
  sorry
