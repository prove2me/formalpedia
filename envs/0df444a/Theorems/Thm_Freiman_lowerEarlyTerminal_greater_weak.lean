-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_greater_weak
-- name    : Freiman.lowerEarlyTerminal_greater_weak
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:47:06.154353+00:00
-- url     : https://prove2.me/theorems/5b25f614-f96c-4350-8e45-6bfba5ef8c23
-- title:
--   Freiman.lowerEarlyTerminal_greater_weak
-- statement:
--   The non-strict field comparison is the existing common-parity Möbius difference formula.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_greater_weak (base : LowerPair) (C : LowerHistoryContext) (hc : C.parity = (false,false))
    (hf : lowerHistoryContextFits base C) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) : section14ComparisonHolds (lowerEarlyTerminalGreater x y false)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
        lowerHistoryValue base C y ≤ lowerHistoryValue base C x := by
  sorry
