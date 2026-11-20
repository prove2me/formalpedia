-- Prove2me | Theorems.Thm_NOF_Protocol_length_broadcast
-- name    : NOF.Protocol.length_broadcast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:04.918441+00:00
-- url     : https://prove2.me/theorems/5ac24d64-0dd1-4245-ba3c-163b4a815989
-- title:
--   Protocol: length broadcast
-- statement:
--   The Protocol construction uses the length broadcast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L46-L48
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L46-L48

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

theorem NOF.Protocol.length_broadcast (P : Protocol G d) (x : ZMod d → G) : ∀ t, (broadcast P x t).length = t
  := by sorry
