-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_ResVal_norm_tower
-- name    : GlobalTheory.UnitLemma.Unr.ResVal.norm_tower
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:36.939867+00:00
-- url     : https://prove2.me/theorems/82a7d615-0cbf-4bc2-9a07-6f6feb13f249
-- title:
--   Res Val: norm tower
-- statement:
--   The Res Val construction uses the norm tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValResultantEqDegreeMulUnramifiedExt.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValResultantEqDegreeMulUnramifiedExt.lean#L76-L83

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

theorem GlobalTheory.UnitLemma.Unr.ResVal.norm_tower {K K' : UQ} (φ : K.E →+* K'.E) (B : InvAlg K) (ψ : K'.E →+* B.A)
    (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (x : B.A) :
    Algebra.norm K.E x = @Algebra.norm K.E K'.E _ _ φ.toAlgebra (@Algebra.norm K'.E B.A _ _ ψ.toAlgebra x) := by sorry
