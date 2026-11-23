-- Prove2me | Theorems.Thm_KernelRank_Component_multiCost_eq_borderCost_add
-- name    : KernelRank.Component.multiCost_eq_borderCost_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:55:22.518284+00:00
-- url     : https://prove2.me/theorems/7aa877de-fe11-4bcd-b432-e80cffcbcb13
-- title:
--   Component: multi Cost eq border Cost add
-- statement:
--   The Component construction uses the multi Cost eq border Cost add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L171-L175
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Defs.lean#L171-L175

import Mathlib
import Definitions.Def_KernelRankLean_Defs
set_option autoImplicit true
open Complex Polynomial
open KernelRank
open KernelRank.Component

theorem KernelRank.Component.multiCost_eq_borderCost_add {d : ℕ} (hd : 2 ≤ d) (c : Component) :
    c.multiCost d = c.borderCost d + (d - 2) * c.poly.natDegree := by sorry
