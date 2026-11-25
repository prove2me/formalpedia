-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock32768
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock32768
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:49:09.957891+00:00
-- url     : https://prove2.me/theorems/c50bc98c-9016-54d9-ab7c-141261500e9b
-- title:
--   R8 opp-bank dimension table, indices 32768–34815
-- statement:
--   For every node index $n$ in the half-open interval $[32768,34816)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock32768 : ∀ n : ℕ, 32768 ≤ n → n < 34816 → nodeCheck n = true := by sorry
