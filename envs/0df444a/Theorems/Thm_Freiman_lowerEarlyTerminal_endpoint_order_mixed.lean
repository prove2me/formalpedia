-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order_mixed
-- name    : Freiman.lowerEarlyTerminal_endpoint_order_mixed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:14.610361+00:00
-- url     : https://prove2.me/theorems/a05dd827-8988-4bda-8d26-91ddef48a9ce
-- title:
--   Freiman.lowerEarlyTerminal_endpoint_order_mixed
-- statement:
--   The mixed-parity virtual-1 endpoint construction has ordered endpoints.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Definitions lowerEndpointWords; full-width normalization and virtual-1 case.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_endpoint_order_mixed (p : LowerPair) (hp : p.1.length % 2 ≠ p.2.length % 2) : lowerEndpoint p false ≤ lowerEndpoint p true := by
  sorry
