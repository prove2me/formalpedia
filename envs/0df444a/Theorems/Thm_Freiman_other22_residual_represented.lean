-- Prove2me | Theorems.Thm_Freiman_other22_residual_represented
-- name    : Freiman.other22_residual_represented
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:35:17.836269+00:00
-- url     : https://prove2.me/theorems/2274699d-09e1-49ec-b955-abf53da51928
-- title:
--   other22 residual represented
-- statement:
--   Expand the actual residual upper endpoint S/21 in the Z parameter coordinates. Its physical pair is reversed relative to (221,312); select the corresponding permitted endpoint case at a width tie, without asserting a false swap identity.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_residual_represented (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S) (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    other22EndpointRepresented Z (other22Context k) other22ResidualWords false (lowerLocalLower S ([2],[1])) := by
  sorry
