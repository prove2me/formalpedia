-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_integralNormVector_pow_sub_mulVec
-- name    : GlobalTheory.PMonE.integralNormVector_pow_sub_mulVec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:40:31.078077+00:00
-- url     : https://prove2.me/theorems/ac1ae10f-dcc9-49da-9c64-60417a0e7da9
-- title:
--   PMon E: integral Norm Vector pow sub mul Vec
-- statement:
--   The PMon E construction uses the integral Norm Vector pow sub mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L22-L30

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

theorem GlobalTheory.PMonE.integralNormVector_pow_sub_mulVec {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (q : ℕ) (x : m → F) (hx : Integral x) :
    Integral (fun i => x i ^ q - A.mulVec x i) := by sorry
