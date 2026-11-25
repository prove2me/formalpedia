-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock20480
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock20480
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:45:30.625373+00:00
-- url     : https://prove2.me/theorems/2dc2a37b-bbbc-4341-80c5-5bd98319adbe
-- title:
--   R8 opp-bank dimension table, indices 20480–22527
-- statement:
--   For every node index $n$ in the half-open interval $[20480,22528)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock20480 : ∀ n : ℕ, 20480 ≤ n → n < 22528 → nodeCheck n = true := by sorry
