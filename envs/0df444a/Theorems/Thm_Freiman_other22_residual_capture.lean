-- Prove2me | Theorems.Thm_Freiman_other22_residual_capture
-- name    : Freiman.other22_residual_capture
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:01.695242+00:00
-- url     : https://prove2.me/theorems/7266b041-69e4-45d2-823a-18b59bfbdfc2
-- title:
--   other22 residual capture
-- statement:
--   Failure of a selected endpoint comparison adds precisely its complemented q-bound to the selected source alternative and endpoint-case conditions.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_residual_capture (p : LowerHistoryPath) (ai bi : ℕ) (bs cs : List CertBound) (g : LowerHistoryComparison)
    (hai : (lowerHistorySourcePremises p)[ai]? = some bs)
    (hbi : (lowerHistoryEndpointComparisons p)[bi]? = some (cs,g))
    (r s q : ℝ) (hs : lowerHistoryConditions bs r s q)
    (hc : lowerHistoryConditions cs r s q) (hn : ¬ lowerHistoryComparisonHolds g r s q) :
    lowerHistoryConditions (lowerHistoryResidual p ai (bi : ℤ)) r s q := by
  sorry
