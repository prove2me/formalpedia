-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie
-- name    : Freiman.lowerEarlyTerminal_endpoint_swap_nontie
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:53.40416+00:00
-- url     : https://prove2.me/theorems/db54a577-b4b2-40e0-9f61-35e27a023e28
-- title:
--   Freiman.lowerEarlyTerminal_endpoint_swap_nontie
-- statement:
--   Swapping incoming words preserves this endpoint when the ordinary normalization and both possible mixed virtual normalizations avoid full-width equality. No endpoint invariance at a tie is asserted.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Endpoint construction lowerEqualWords/lowerEndpointWords, retaining the incoming side at equality.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_endpoint_swap_nontie (w : LowerPair) (hn : LowerEarlyTerminalNoTies w) (upper : Bool) :
    lowerEndpoint w upper = lowerEndpoint (w.2,w.1) upper := by
  sorry
