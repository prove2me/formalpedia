-- Prove2me | Theorems.Thm_NOF_Protocol_broadcast_succ
-- name    : NOF.Protocol.broadcast_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:07.444413+00:00
-- url     : https://prove2.me/theorems/4c77ec18-3ece-45d7-9405-16934592323a
-- title:
--   Protocol: broadcast succ
-- statement:
--   The Protocol construction uses the broadcast succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L38-L40
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L38-L40

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
open NOF.Protocol

theorem NOF.Protocol.broadcast_succ (P : Protocol G d) (x : ZMod d → G) (t : ℕ) :
    broadcast P x (t + 1)
      = P.nextBit t (forget (t : ZMod d) x) (broadcast P x t) :: broadcast P x t := by sorry
