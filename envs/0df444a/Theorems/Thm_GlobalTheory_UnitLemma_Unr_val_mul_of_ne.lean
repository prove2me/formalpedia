-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_val_mul_of_ne
-- name    : GlobalTheory.UnitLemma.Unr.val_mul_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:35.629037+00:00
-- url     : https://prove2.me/theorems/444a16cf-3dd3-4747-9a6d-a100d72b8f46
-- title:
--   Unr: val mul of ne
-- statement:
--   The Unr construction uses the val mul of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaGramDetInvAlgBaseChangeUnramifiedOdd.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaGramDetInvAlgBaseChangeUnramifiedOdd.lean#L14-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsBasisTraceInvolutionDetUnitUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetTraceGramBlockMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaGramDetInvAlgBaseChangeUnramifiedOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem GlobalTheory.UnitLemma.Unr.val_mul_of_ne {K : UQ} {a b : K.E} (ha : a ≠ 0) (hb : b ≠ 0) :
    val K.O (a * b) = val K.O a + val K.O b := by sorry
