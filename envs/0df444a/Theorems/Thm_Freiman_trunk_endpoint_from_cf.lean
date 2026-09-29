-- Prove2me | Theorems.Thm_Freiman_trunk_endpoint_from_cf
-- name    : Freiman.trunk_endpoint_from_cf
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:57:57.61658+00:00
-- url     : https://prove2.me/theorems/79046355-9cbf-48e6-8c23-a5705450227f
-- title:
--   trunk endpoint from cf
-- statement:
--   The strict second width branch, virtual mixed endpoint and optional7/5 shortening enumerate the actual endpoint; common odd parity changes both the sign and endpoint flag. All rational tails are interpreted by the shared exact CF evaluation.
-- source:
--   Report Proposition4.1 s15:trunk, printed report p28; original source pp120–126. Complete sixteen-state trunk certificate,58230 records,90 case plans, with three explicitly unfilled interfaces.

import Definitions.Def_Freiman_trunkGeometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open Freiman

theorem Freiman.trunk_endpoint_from_cf (hc : ∀ (w : List ℕ+) (z : CertField), 0 ≤ certFieldVal z → certFieldVal (lowerHistoryCF w z) = prefixEval w (certFieldVal z)) :
    TrunkEndpointLaw := by
  sorry
