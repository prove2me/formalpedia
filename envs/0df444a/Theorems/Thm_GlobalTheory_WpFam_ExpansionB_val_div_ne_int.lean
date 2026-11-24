-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_ExpansionB_val_div_ne_int
-- name    : GlobalTheory.WpFam.ExpansionB.val_div_ne_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:47.169061+00:00
-- url     : https://prove2.me/theorems/667dee35-1e63-4c3f-aa04-77dd496cc70b
-- title:
--   Expansion B: val div ne int
-- statement:
--   The Expansion B construction uses the val div ne int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassDivisionValueQExpansion.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WeierstrassDivisionValueQExpansion.lean#L12-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointRowsSumEqDivisorSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_G2AddWeierstrassPRowSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeierstrassDivisionValueQExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.ExpansionB

theorem GlobalTheory.WpFam.ExpansionB.val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by sorry
