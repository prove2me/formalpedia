-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_val_norm
-- name    : GlobalTheory.UnitLemma.Unr.ResVal.val_norm
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:46:49.725243+00:00
-- url     : https://prove2.me/theorems/b7ad3887-edeb-466c-ac3d-724f2335e049
-- title:
--   Res Val: val norm
-- statement:
--   The Res Val construction uses the val norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValResultantEqDegreeMulUnramifiedExt.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValResultantEqDegreeMulUnramifiedExt.lean#L21-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CharpolyLeftMulBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SeparableCharpolyInvAlgBaseChangeUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegerMapIsIntegralUnramifiedInvolutionExStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvrFractionFieldAddValNormUnramifiedLocalExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGeneratesUnramifiedExtResidueFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotIsRootResidueCofactorUnramifiedExtStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValResultantEqDegreeMulUnramifiedExt
import Theorems.Thm_GlobalTheory_UnitLemma_Unr_NormValU_val_norm

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
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.ResVal

theorem GlobalTheory.UnitLemma.Unr.ResVal.val_norm : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ y : K'.E,
    val K.O (@Algebra.norm K.E K'.E _ _ φ.toAlgebra y) = (d : ℤ) * val K'.O y := by sorry
