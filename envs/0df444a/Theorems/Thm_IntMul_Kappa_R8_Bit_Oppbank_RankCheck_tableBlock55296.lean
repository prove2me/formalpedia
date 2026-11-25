-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock55296
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock55296
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:49:16.674033+00:00
-- url     : https://prove2.me/theorems/1cf2ed02-f099-5e3b-b96c-76eff51a47f2
-- title:
--   R8 opp-bank dimension table, indices 55296–57343
-- statement:
--   For every node index $n$ in the half-open interval $[55296,57344)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock55296 : ∀ n : ℕ, 55296 ≤ n → n < 57344 → nodeCheck n = true := by sorry
