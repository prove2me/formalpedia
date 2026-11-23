-- Prove2me | Theorems.Thm_KernelRank_Component_multiCost_two
-- name    : KernelRank.Component.multiCost_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:55:05.200387+00:00
-- url     : https://prove2.me/theorems/7ce46daa-238f-401e-a950-0cacfe833395
-- title:
--   Component: multi Cost two
-- statement:
--   The Component construction uses the multi Cost two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L156-L158
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L156-L158

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank
open KernelRank.Component

theorem KernelRank.Component.multiCost_two (c : Component) : c.multiCost 2 = c.cost := by sorry
