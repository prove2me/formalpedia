-- Prove2me | Theorems.Thm_GridHam_accA_eq
-- name    : GridHam.accA_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:34:52.573843+00:00
-- url     : https://prove2.me/theorems/573cf249-96a5-4368-b369-64a28c6e18a9
-- title:
--   Grid Ham: acc A eq
-- statement:
--   The Grid Ham construction uses the acc A eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L73-L74
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L73-L74

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_eq (w h sx sy tx ty : ℕ) :
    AccA w h sx sy tx ty ↔ CCA w h sx sy tx ty ∧ ¬ ForbA w h sx sy tx ty := by sorry
