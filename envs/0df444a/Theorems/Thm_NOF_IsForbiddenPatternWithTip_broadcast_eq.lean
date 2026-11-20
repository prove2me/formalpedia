-- Prove2me | Theorems.Thm_NOF_IsForbiddenPatternWithTip_broadcast_eq
-- name    : NOF.IsForbiddenPatternWithTip.broadcast_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:10.35812+00:00
-- url     : https://prove2.me/theorems/815a66b9-75b7-4e2f-b492-ae2dc624eceb
-- title:
--   Is Forbidden Pattern With Tip: broadcast eq
-- statement:
--   The Is Forbidden Pattern With Tip construction uses the broadcast eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L64-L77
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L64-L77

module
public import Definitions.Def_ChandraFurstLipton_MultidimCorners
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.ZMod.Defs
public import Definitions.Def_ChandraFurstLipton_NOFModel
set_option autoImplicit false
@[expose] public section
public section
open NOF
variable {ι G : Type*} {d : ℕ} [Fintype ι]
variable {F : (ZMod d → G) → Bool} {P : Protocol G d} {a : ZMod d → ZMod d → G} {v : ZMod d → G}
  {B : List Bool} {t : ℕ}

theorem NOF.IsForbiddenPatternWithTip.broadcast_eq (hF : IsForbiddenPatternWithTip a v)
    (hB : ∀ i, P.broadcast (a i) t = B) : P.broadcast v t = B := by sorry
