-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_additiveSystemFrobeniusPowerSum_zero
-- name    : GlobalTheory.PMonE.additiveSystemFrobeniusPowerSum_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:38:58.717177+00:00
-- url     : https://prove2.me/theorems/867e12f4-f86a-46ed-ab51-e2009b074a7b
-- title:
--   PMon E: additive System Frobenius Power Sum zero
-- statement:
--   The PMon E construction uses the additive System Frobenius Power Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemGeneralLemmaOrderOne.lean#L32-L38

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

theorem GlobalTheory.PMonE.additiveSystemFrobeniusPowerSum_zero {F : Type} [NormedField F] {m : Type} [Fintype m] (q D : ℕ) (hq : 0 < q)
    (U : ℕ → Matrix m m F) : gsum q D U (fun _ => 0) = 0 := by sorry
