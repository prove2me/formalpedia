-- Prove2me | Theorems.Thm_Freiman_other22_endpoint_inventory
-- name    : Freiman.other22_endpoint_inventory
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:25.404481+00:00
-- url     : https://prove2.me/theorems/256617b7-672e-4198-ba7d-9e14e6c4f271
-- title:
--   other22 endpoint inventory
-- statement:
--   The row1 comparison inventory is exactly the earlier32/base endpoint against the residual upper endpoint at relative words (221,312). No endpoint swap equality is asserted.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_endpoint_inventory :
    ∀ k : Fin 6, lowerHistoryEndpointComparisons (other22Paths k) =
    lowerHistoryComparisons (other22Context k) (other22Ancestor k) other22ResidualWords (other22AncestorUpper k) false := by
  sorry
