-- Prove2me | Theorems.Thm_GlobalTheory_commute_rightDerivEnd_leftTranslate
-- name    : GlobalTheory.commute_rightDerivEnd_leftTranslate
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:24.53605+00:00
-- url     : https://prove2.me/theorems/fae91b1e-6f7b-4dd3-a002-e4e1523b26a9
-- title:
--   Global Theory: commute right Deriv End left Translate
-- statement:
--   The Global Theory construction uses the commute right Deriv End left Translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftTranslateSmoothCommuteLeftInvariantOps.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftTranslateSmoothCommuteLeftInvariantOps.lean#L31-L36

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem GlobalTheory.commute_rightDerivEnd_leftTranslate (h : IsExpLieAlgebra G 𝔤) (g : G) (X : 𝔤) :
    Commute (h.rightDerivEnd (F := ℂ) X) (leftTranslateSmoothEnd h g) := by sorry
