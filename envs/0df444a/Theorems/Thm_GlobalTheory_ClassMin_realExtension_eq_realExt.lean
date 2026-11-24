-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_realExtension_eq_realExt
-- name    : GlobalTheory.ClassMin.realExtension_eq_realExt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:40.004305+00:00
-- url     : https://prove2.me/theorems/f99bb930-9e8a-4215-99ec-9b441778ce44
-- title:
--   Class Min: real Extension eq real Ext
-- statement:
--   The Class Min construction uses the real Extension eq real Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsShiftedLtClassMin.lean#L62-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}

theorem GlobalTheory.ClassMin.realExtension_eq_realExt (Q : QuadraticMap ℤ X ℝ) : realExtension Q = realExt Q := by sorry
