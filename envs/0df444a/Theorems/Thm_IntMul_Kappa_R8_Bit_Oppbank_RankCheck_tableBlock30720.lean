-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock30720
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock30720
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:45:47.895325+00:00
-- url     : https://prove2.me/theorems/e7af9cda-2abc-48c7-8106-77377f71f113
-- title:
--   R8 opp-bank dimension table, indices 30720–32767
-- statement:
--   For every node index $n$ in the half-open interval $[30720,32768)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock30720 : ∀ n : ℕ, 30720 ≤ n → n < 32768 → nodeCheck n = true := by sorry
