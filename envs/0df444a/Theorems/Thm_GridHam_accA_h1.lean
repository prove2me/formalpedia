-- Prove2me | Theorems.Thm_GridHam_accA_h1
-- name    : GridHam.accA_h1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:35:13.43013+00:00
-- url     : https://prove2.me/theorems/d2b8bd4e-8b99-4ad2-8cab-c40b13b195ed
-- title:
--   Grid Ham: acc A h1
-- statement:
--   The Grid Ham construction uses the acc A h1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L86-L102
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L86-L102

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_h1 (w sx sy tx ty : ℕ) (hw : 2 ≤ w) :
    AccA w 1 sx sy tx ty ↔ CCA w 1 sx sy tx ty ∧ EndsA w sx sy tx ty := by sorry
