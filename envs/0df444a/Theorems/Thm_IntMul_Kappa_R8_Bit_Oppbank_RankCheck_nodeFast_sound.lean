-- Prove2me | Theorems.Thm_IntMul_Kappa_R8_Bit_Oppbank_RankCheck_nodeFast_sound
-- name    : IntMul.Kappa.R8.Bit.Oppbank.RankCheck.nodeFast_sound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T07:32:16.858803+00:00
-- url     : https://prove2.me/theorems/9012ff2e-9759-59e0-b614-46426cfb05d7
-- title:
--   Soundness of the structural rank checks for R8
-- statement:
--   If the structural checker accepts the dimension entry of a densified node, the original sparse-elimination check accepts that entry. This allows the finite table verification to use the graph’s structure when it is recognized.
-- source:
--   Rank-table verification for IntMul.Kappa.R8.Bit.Oppbank.Pc_rank_ND, https://prove2.me/theorems/590a9ee0-cecb-41be-b425-cdf41014939d

import Definitions.Def_IntMul_Kappa_R8_OppbankRankFast

open IntMul.Kappa.R8.Bit.Oppbank.RankCheck

theorem IntMul.Kappa.R8.Bit.Oppbank.RankCheck.nodeFast_sound {n : ℕ} (h : nodeFast n = true) : nodeCheck n = true := by sorry
