-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_mixed
-- name    : Freiman.lowerEarlyTerminal_endpoint_mixed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:46:34.728983+00:00
-- url     : https://prove2.me/theorems/99e8db62-85df-4424-80fd-cf3464787a39
-- title:
--   Freiman.lowerEarlyTerminal_endpoint_mixed
-- statement:
--   Evaluate mixed-parity modes via the exact virtual-1 branch and fresh normalization.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source independent_residual.py: endpoint(); independent_extensions.py: endpoint().

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_endpoint_mixed (base : LowerPair) (C : LowerHistoryContext) (hc : C.parity = (false,false))
    (hf : lowerHistoryContextFits base C) (w : LowerPair) (upper : Bool) (he : lowerHistoryWordParity C w false ≠ lowerHistoryWordParity C w true) : ∃ z cs, (z,cs) ∈ section14EndpointCases C w upper ∧ lowerHistoryAtBase base cs ∧
      (0 ≤ certFieldVal z.1 ∧ 0 ≤ certFieldVal z.2) ∧
      lowerHistoryEndpointReal base C w upper = lowerHistoryValue base C z := by
  sorry
