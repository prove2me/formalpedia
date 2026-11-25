-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock61440
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock61440
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:46:46.924014+00:00
-- url     : https://prove2.me/theorems/4ff55c2c-4ea5-484c-97bd-ca8976f6279e
-- title:
--   R8 opp-bank dimension table, indices 61440–62477
-- statement:
--   For every node index $n$ in the half-open interval $[61440,62478)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock61440 : ∀ n : ℕ, 61440 ≤ n → n < 62478 → nodeCheck n = true := by sorry
