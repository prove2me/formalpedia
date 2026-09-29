-- Prove2me | Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_order
-- name    : Freiman.lowerEarlyTerminal_endpoint_order
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T13:41:17.452609+00:00
-- url     : https://prove2.me/theorems/1a21912a-5177-4889-b108-da137c608927
-- title:
--   Freiman.lowerEarlyTerminal_endpoint_order
-- statement:
--   Every source cover has ordered endpoints, including mixed parity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert.

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry

open Freiman

theorem Freiman.lowerEarlyTerminal_endpoint_order (p : LowerPair) : lowerEndpoint p false ≤ lowerEndpoint p true := by
  sorry
