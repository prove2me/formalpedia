-- Prove2me | Theorems.Thm_GlobalTheory_leftTranslate_smooth_commute
-- name    : GlobalTheory.leftTranslate_smooth_commute
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:56:33.173363+00:00
-- url     : https://prove2.me/theorems/63400f20-82f6-4945-871c-aff44ce3f272
-- title:
--   Global Theory: left Translate smooth commute
-- statement:
--   The Global Theory construction uses the left Translate smooth commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftTranslateSmoothCommuteLeftInvariantOps.lean#L38-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftTranslateSmoothCommuteLeftInvariantOps.lean#L38-L50

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

theorem GlobalTheory.leftTranslate_smooth_commute (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸)
    (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G) :
    ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧
      ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y,
        (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by sorry
