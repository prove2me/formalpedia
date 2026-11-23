-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_val_mul_ne
-- name    : GlobalTheory.UnitLemma.Unr.NormValU.val_mul_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:50.058797+00:00
-- url     : https://prove2.me/theorems/5985b3bf-03f7-491c-a208-ada834186965
-- title:
--   Norm Val U: val mul ne
-- statement:
--   The Norm Val U construction uses the val mul ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrFractionFieldAddValNormUnramifiedLocalExt.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrFractionFieldAddValNormUnramifiedLocalExt.lean#L15-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIntegersUnramifiedInvolutionExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.NormValU
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E]

theorem GlobalTheory.UnitLemma.Unr.NormValU.val_mul_ne {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : val O (x * y) = val O x + val O y := by sorry
