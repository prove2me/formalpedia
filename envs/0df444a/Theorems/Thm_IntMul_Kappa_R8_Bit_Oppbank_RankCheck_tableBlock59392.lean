-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock59392
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock59392
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:49:24.37624+00:00
-- url     : https://prove2.me/theorems/f849c24b-0f82-586d-9e76-2d01d40d2c04
-- title:
--   R8 opp-bank dimension table, indices 59392–61439
-- statement:
--   For every node index $n$ in the half-open interval $[59392,61440)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock59392 : ∀ n : ℕ, 59392 ≤ n → n < 61440 → nodeCheck n = true := by sorry
