-- Prove2me | Theorems.Thm_GridHam_accA_h3
-- name    : GridHam.accA_h3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:36:27.591153+00:00
-- url     : https://prove2.me/theorems/40a9d766-37af-4397-af9c-974e26f1f101
-- title:
--   Grid Ham: acc A h3
-- statement:
--   The Grid Ham construction uses the acc A h3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L118-L133
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L118-L133

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_h3 (w sx sy tx ty : ℕ) (hw : 4 ≤ w) :
    AccA w 3 sx sy tx ty ↔
      CCA w 3 sx sy tx ty ∧ ¬ G3 w sx tx sy ((sx + sy) % 2) ((tx + ty) % 2) := by sorry
