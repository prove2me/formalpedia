-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock02048
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock02048
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T06:46:09.935962+00:00
-- url     : https://prove2.me/theorems/056f1def-b749-4688-8925-4e2cfdec0af2
-- title:
--   R8 opp-bank dimension table, indices 2048–4095
-- statement:
--   For every node index $n$ in the half-open interval $[2048,4096)$, the sparse rank checker accepts the published dimension entry. The interval is one part of the rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4000

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock02048 : ∀ n : ℕ, 2048 ≤ n → n < 4096 → nodeCheck n = true := by sorry
