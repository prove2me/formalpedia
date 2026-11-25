-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock36864
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock36864
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:46:18.563721+00:00
-- url     : https://prove2.me/theorems/2398c4a4-5280-4bf8-8de6-a2d2e7589738
-- title:
--   R8 opp-bank dimension table, indices 36864–38911
-- statement:
--   For every node index $n$ in the half-open interval $[36864,38912)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock36864 : ∀ n : ℕ, 36864 ≤ n → n < 38912 → nodeCheck n = true := by sorry
