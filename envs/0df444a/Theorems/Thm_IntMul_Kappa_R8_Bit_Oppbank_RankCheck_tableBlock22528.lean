-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock22528
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock22528
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:44:58.2279+00:00
-- url     : https://prove2.me/theorems/a27b0149-b19a-4422-8284-34f5e116c28b
-- title:
--   R8 opp-bank dimension table, indices 22528–24575
-- statement:
--   For every node index $n$ in the half-open interval $[22528,24576)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock22528 : ∀ n : ℕ, 22528 ≤ n → n < 24576 → nodeCheck n = true := by sorry
