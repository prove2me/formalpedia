-- Prove2me | Theorems.Thm_KernelRank_Component_eval_eq
-- name    : KernelRank.Component.eval_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:34:52.187802+00:00
-- url     : https://prove2.me/theorems/9a1d9dc4-d11d-4210-813e-494bb5ca8f3b
-- title:
--   Component: eval eq
-- statement:
--   The Component construction uses the eval eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean#L17-L17
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Representation.lean#L17-L17

import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_Defs
import Definitions.Def_KernelRankLean_Representation
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.Component.eval_eq (c : Component) (s : ℝ) : c.eval s = (expPoly c.poly c.rate s).re := by sorry
