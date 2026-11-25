-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock24576
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock24576
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:52:21.775634+00:00
-- url     : https://prove2.me/theorems/e5f4c12d-cbb1-4dc8-bf98-65dd485f6e48
-- title:
--   R8 opp-bank dimension table, indices 24576–26623
-- statement:
--   For every node index $n$ in $[24576,26624)$, the sparse rank checker accepts the published dimension entry. This interval is one part of the finite rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock24576 : ∀ n : ℕ, 24576 ≤ n → n < 26624 → nodeCheck n = true := by sorry
