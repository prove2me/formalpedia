-- Prove2me | Theorems.Thm_GridHam_accA_w2
-- name    : GridHam.accA_w2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:41:32.000876+00:00
-- url     : https://prove2.me/theorems/d53d6a9d-1a61-47b6-8d8d-9de9573ec7ec
-- title:
--   Grid Ham: acc A w2
-- statement:
--   The Grid Ham construction uses the acc A w2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L153-L165
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L153-L165

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_w2 (h sx sy tx ty : ℕ) (hh : 2 ≤ h) :
    AccA 2 h sx sy tx ty ↔ CCA 2 h sx sy tx ty ∧ ¬ F2A 2 h sx sy tx ty := by sorry
