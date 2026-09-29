-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_greater_strict
-- name    : Freiman.lowerEarlyTerminal_greater_strict
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:45:49.32646+00:00
-- url     : https://prove2.me/theorems/8acb0291-45cf-496c-83aa-bc073c4c5c88
-- title:
--   Freiman.lowerEarlyTerminal_greater_strict
-- statement:
--   Strict comparison handles equality, opposite signs and the positive full-width scale explicitly.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_greater_strict (base : LowerPair) (C : LowerHistoryContext) (hc : C.parity = (false,false))
    (hf : lowerHistoryContextFits base C) (x y : CertField × CertField)
    (hx : 0 ≤ certFieldVal x.1 ∧ 0 ≤ certFieldVal x.2)
    (hy : 0 ≤ certFieldVal y.1 ∧ 0 ≤ certFieldVal y.2) : section14ComparisonHolds (lowerEarlyTerminalGreater x y true)
      (lowerRatio base.1) (lowerRatio base.2) (lowerScale base) ↔
        lowerHistoryValue base C y < lowerHistoryValue base C x := by
  sorry
