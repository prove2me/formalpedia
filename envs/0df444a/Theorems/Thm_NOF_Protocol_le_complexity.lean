-- Prove2me | Theorems.Thm_NOF_Protocol_le_complexity
-- name    : NOF.Protocol.le_complexity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:03.682176+00:00
-- url     : https://prove2.me/theorems/a24bd7dd-816c-4983-9322-80d377ec6577
-- title:
--   Protocol: le complexity
-- statement:
--   The Protocol construction uses the le complexity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L54-L55
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L54-L55

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

theorem NOF.Protocol.le_complexity : t ≤ Protocol.complexity P F ↔ ∀ r : ℕ, P.IsValid F r → t ≤ r := by sorry
