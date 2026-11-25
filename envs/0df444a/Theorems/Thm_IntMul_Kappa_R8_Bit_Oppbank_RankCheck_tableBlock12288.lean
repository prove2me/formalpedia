-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock12288
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock12288
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:45:42.299321+00:00
-- url     : https://prove2.me/theorems/d047c68b-305a-4d50-add8-b7a092c80f0c
-- title:
--   R8 opp-bank dimension table, indices 12288–14335
-- statement:
--   For every node index $n$ in the half-open interval $[12288,14336)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock12288 : ∀ n : ℕ, 12288 ≤ n → n < 14336 → nodeCheck n = true := by sorry
