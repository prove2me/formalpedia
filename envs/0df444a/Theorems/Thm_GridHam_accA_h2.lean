-- Prove2me | Theorems.Thm_GridHam_accA_h2
-- name    : GridHam.accA_h2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:35:02.391809+00:00
-- url     : https://prove2.me/theorems/4d37783e-b050-47d1-a20d-4a212cefea3b
-- title:
--   Grid Ham: acc A h2
-- statement:
--   The Grid Ham construction uses the acc A h2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L104-L116
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L104-L116

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_h2 (w sx sy tx ty : ℕ) (hw : 3 ≤ w) :
    AccA w 2 sx sy tx ty ↔ CCA w 2 sx sy tx ty ∧ ¬ F2A w 2 sx sy tx ty := by sorry
