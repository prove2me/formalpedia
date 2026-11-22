-- Prove2me | Theorems.Thm_GridHam_accA_w3
-- name    : GridHam.accA_w3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:44:58.002814+00:00
-- url     : https://prove2.me/theorems/45a0df50-811c-4743-97d9-f99c965c6a9e
-- title:
--   Grid Ham: acc A w3
-- statement:
--   The Grid Ham construction uses the acc A w3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L167-L182
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L167-L182

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_w3 (h sx sy tx ty : ℕ) (hh : 4 ≤ h) :
    AccA 3 h sx sy tx ty ↔
      CCA 3 h sx sy tx ty ∧ ¬ G3 h sy ty sx ((sx + sy) % 2) ((tx + ty) % 2) := by sorry
