-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_norm_mulVec_le_one_of_integral_matrix
-- name    : GlobalTheory.PMonE.norm_mulVec_le_one_of_integral_matrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:40:49.85538+00:00
-- url     : https://prove2.me/theorems/71dd3542-928d-41ee-9d34-ecdffa8df7ca
-- title:
--   PMon E: norm mul Vec le one of integral matrix
-- statement:
--   The PMon E construction uses the norm mul Vec le one of integral matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L14-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangCountFrobeniusEqMulVecSolutionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset

theorem GlobalTheory.PMonE.norm_mulVec_le_one_of_integral_matrix {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F) (hx : Integral x) (i : m) :
    ‖A.mulVec x i‖ ≤ 1 := by sorry
