-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock51200
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock51200
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:49:31.69479+00:00
-- url     : https://prove2.me/theorems/162e4a8e-88a2-5089-9348-7c0718d5f154
-- title:
--   R8 opp-bank dimension table, indices 51200–53247
-- statement:
--   For every node index $n$ in the half-open interval $[51200,53248)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock51200 : ∀ n : ℕ, 51200 ≤ n → n < 53248 → nodeCheck n = true := by sorry
