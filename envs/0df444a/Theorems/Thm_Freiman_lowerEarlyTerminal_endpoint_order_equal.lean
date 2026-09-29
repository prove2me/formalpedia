-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order_equal
-- name    : Freiman.lowerEarlyTerminal_endpoint_order_equal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:42:26.023047+00:00
-- url     : https://prove2.me/theorems/3e5f523d-4697-4ffd-b5d3-ade0e1f73876
-- title:
--   Freiman.lowerEarlyTerminal_endpoint_order_equal
-- statement:
--   The two natural/shortened endpoints are ordered in the equal-parity construction.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Definitions lowerEqualWords; report endpoint construction before the scalar appendices.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_endpoint_order_equal (p : LowerPair) (hp : p.1.length % 2 = p.2.length % 2) : lowerEndpoint p false ≤ lowerEndpoint p true := by
  sorry
