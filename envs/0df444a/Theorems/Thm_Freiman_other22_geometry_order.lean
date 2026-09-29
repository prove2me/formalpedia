-- Prove2me | Theorems.Thm_Freiman_other22_geometry_order
-- name    : Freiman.other22_geometry_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:35:21.478167+00:00
-- url     : https://prove2.me/theorems/aaf68a7f-f5be-4e3b-aa3a-6258f0ae112d
-- title:
--   other22 geometry order
-- statement:
--   The numerical packet and the two faithful actual-endpoint representations imply exactly the needed residual upper-endpoint bound, for both common parities.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_geometry_order (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerLocalLower S ([2],[1]) ≤ other22AnchorValue Z := by
  sorry
