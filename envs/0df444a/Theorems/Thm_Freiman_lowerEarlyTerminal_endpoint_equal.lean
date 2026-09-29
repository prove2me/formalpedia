-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_equal
-- name    : Freiman.lowerEarlyTerminal_endpoint_equal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:59.262755+00:00
-- url     : https://prove2.me/theorems/188abc43-e5d6-4913-80d1-a33b3a8f7167
-- title:
--   Freiman.lowerEarlyTerminal_endpoint_equal
-- statement:
--   Evaluate same-parity endpoint modes and auxiliary shortening with strict right-width normalization, retaining the incoming side at equality.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source independent_residual.py: equal(); independent_extensions.py: equal().

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_endpoint_equal (base : LowerPair) (C : LowerHistoryContext) (hc : C.parity = (false,false))
    (hf : lowerHistoryContextFits base C) (w : LowerPair) (upper : Bool) (he : lowerHistoryWordParity C w false = lowerHistoryWordParity C w true) : ∃ z cs, (z,cs) ∈ section14EndpointCases C w upper ∧ lowerHistoryAtBase base cs ∧
      (0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2) ∧
      lowerHistoryEndpointReal base C w upper = lowerHistoryValue base C z := by
  sorry
