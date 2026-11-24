-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_exists_val_one
-- name    : GlobalTheory.UnitLemma.Unr.NormValU.exists_val_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:36:37.315691+00:00
-- url     : https://prove2.me/theorems/2cbe0a88-ed24-403a-9c17-403fa4695a6c
-- title:
--   Norm Val U: exists val one
-- statement:
--   The Norm Val U construction uses the exists val one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrFractionFieldAddValNormUnramifiedLocalExt.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvrFractionFieldAddValNormUnramifiedLocalExt.lean#L52-L54

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

theorem GlobalTheory.UnitLemma.Unr.NormValU.exists_val_one : ∃ π : E, val O π = 1 := by sorry
