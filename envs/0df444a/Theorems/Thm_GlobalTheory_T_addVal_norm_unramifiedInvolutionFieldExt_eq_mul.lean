-- Prove2me | Theorems.Thm_GlobalTheory_T_addVal_norm_unramifiedInvolutionFieldExt_eq_mul
-- name    : GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:00.553427+00:00
-- url     : https://prove2.me/theorems/ff08f0b2-46be-4bd8-9897-17beaec40de2
-- title:
--   T: add Val norm unramified Involution Field Ext eq mul
-- statement:
--   The T construction uses the add Val norm unramified Involution Field Ext eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMulStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMulStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMulStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.addVal_norm_unramifiedInvolutionFieldExt_eq_mul : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → 0 < d → ∀ y : K'.E, val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = d * val K'.O y := by sorry
