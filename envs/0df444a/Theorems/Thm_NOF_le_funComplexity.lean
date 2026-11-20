-- Prove2me | Theorems.Thm_NOF_le_funComplexity
-- name    : NOF.le_funComplexity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T18:14:05.462322+00:00
-- url     : https://prove2.me/theorems/c5f26020-d69c-43c1-8110-aae96c9397a0
-- title:
--   NOF: le fun Complexity
-- statement:
--   The NOF construction uses the le fun Complexity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L61-L62
-- source:
--   https://github.com/YaelDillies/chandra-furst-lipton/blob/95c7ea0802c195bef2238ad962873c0907f1f8a9/ChandraFurstLipton/NOFModel.lean#L61-L62

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

theorem NOF.le_funComplexity : t ≤ funComplexity F ↔ ∀ P : Protocol G d, t ≤ P.complexity F := by sorry
