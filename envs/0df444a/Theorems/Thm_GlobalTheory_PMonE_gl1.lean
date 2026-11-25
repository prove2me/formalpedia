-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_gl1
-- name    : GlobalTheory.PMonE.gl1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:36.395351+00:00
-- url     : https://prove2.me/theorems/3269a777-418c-4a6b-8a52-d9292f1af413
-- title:
--   PMon E: gl1
-- statement:
--   The PMon E construction uses the gl1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L40-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L40-L80

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

theorem GlobalTheory.PMonE.gl1 : GLOnto 1 ∧ GLCount 1 := by sorry
