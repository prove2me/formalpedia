-- Prove2me | Theorems.Thm_GridHam_accA_w1
-- name    : GridHam.accA_w1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T21:43:58.845101+00:00
-- url     : https://prove2.me/theorems/ed6ad50a-3620-4cb4-9c01-0014a768b91c
-- title:
--   Grid Ham: acc A w1
-- statement:
--   The Grid Ham construction uses the acc A w1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L135-L151
-- source:
--   https://github.com/zzyzek/GridHam2D-Lean/blob/45eec4d0c85c2d5b6d44a6bf032b2092536cecac/GridHam/Reduction.lean#L135-L151

module
public import Definitions.Def_GridHam_Arith
public import Definitions.Def_GridHam_PrimeTable
public import Definitions.Def_GridHam_Reduction
set_option autoImplicit true
@[expose] public section
public section
open GridHam

theorem GridHam.accA_w1 (h sx sy tx ty : ℕ) (_hh : 2 ≤ h) :
    AccA 1 h sx sy tx ty ↔ CCA 1 h sx sy tx ty ∧ EndsV h sx sy tx ty := by sorry
