-- Prove2me | Theorems.Thm_GlobalTheory_T_leftTranslate_smooth_commute_leftInvariantOps
-- name    : GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:04:47.298172+00:00
-- url     : https://prove2.me/theorems/6b970704-f4d4-49b4-8afc-0c7f6d4e768e
-- title:
--   T: left Translate smooth commute left Invariant Ops
-- statement:
--   The T construction uses the left Translate smooth commute left Invariant Ops property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftTranslateSmoothCommuteLeftInvariantOpsStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LeftTranslateSmoothCommuteLeftInvariantOpsStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOps
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G), ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by sorry
