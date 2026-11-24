-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormVal_val_algebraMap_unit
-- name    : GlobalTheory.UnitLemma.Unr.NormVal.val_algebraMap_unit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:35:41.118849+00:00
-- url     : https://prove2.me/theorems/d7bea74c-b82a-4651-9ddc-e12b2e3ac924
-- title:
--   Norm Val: val algebra Map unit
-- statement:
--   The Norm Val construction uses the val algebra Map unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AddValNormUnramifiedInvolutionFieldExtEqMul.lean#L46-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralBasisUnramifiedInvolutionExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddValNormUnramifiedInvolutionFieldExtEqMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormVal
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

theorem GlobalTheory.UnitLemma.Unr.NormVal.val_algebraMap_unit (a : O) (ha : IsUnit a) : val O (algebraMap O E a) = 0 := by sorry
