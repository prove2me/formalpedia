-- Prove2me | Theorems.Thm_KernelRank_multiTotalCost_two
-- name    : KernelRank.multiTotalCost_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:51:07.096839+00:00
-- url     : https://prove2.me/theorems/35831841-66bf-4bf0-b352-973ff4fffd43
-- title:
--   Kernel Rank: multi Total Cost two
-- statement:
--   The Kernel Rank construction uses the multi Total Cost two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L218-L221
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L218-L221

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.multiTotalCost_two (cs : List Component) : multiTotalCost 2 cs = totalCost cs := by sorry
