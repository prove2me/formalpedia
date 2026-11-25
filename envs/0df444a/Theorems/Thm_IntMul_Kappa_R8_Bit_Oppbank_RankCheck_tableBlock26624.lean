-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_tableBlock26624
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock26624
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T06:52:07.422553+00:00
-- url     : https://prove2.me/theorems/e6ab5e50-34cc-5883-b914-0d73992b4365
-- title:
--   R8 opp-bank dimension table, indices 26624–28671
-- statement:
--   For every node index $n$ in $[26624,28672)$, the sparse rank checker accepts the published dimension entry. This interval is one part of the finite rank-table check for the densified ND projectors.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankCheck
open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.tableBlock26624 : ∀ n : ℕ, 26624 ≤ n → n < 28672 → nodeCheck n = true := by sorry
