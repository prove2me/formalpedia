-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock45056
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock45056
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:46:17.567806+00:00
-- url     : https://prove2.me/theorems/3ffa6dbf-4204-4274-aec1-ab0f66501fd0
-- title:
--   R8 opp-bank dimension table, indices 45056–47103
-- statement:
--   For every node index $n$ in the half-open interval $[45056,47104)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock45056 : ∀ n : ℕ, 45056 ≤ n → n < 47104 → nodeCheck n = true := by sorry
