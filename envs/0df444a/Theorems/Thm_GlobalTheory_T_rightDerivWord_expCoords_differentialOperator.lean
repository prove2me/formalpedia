-- Prove2me | Theorems.Thm_GlobalTheory_T_rightDerivWord_expCoords_differentialOperator
-- name    : GlobalTheory.T.rightDerivWord_expCoords_differentialOperator
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:22.109744+00:00
-- url     : https://prove2.me/theorems/9ad3d107-21b2-4875-9f72-46491898263f
-- title:
--   T: right Deriv Word exp Coords differential Operator
-- statement:
--   The T construction uses the right Deriv Word exp Coords differential Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightDerivWordExpCoordsDifferentialOperatorStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightDerivWordExpCoordsDifferentialOperatorStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperator
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperatorStatement
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

theorem GlobalTheory.T.rightDerivWord_expCoords_differentialOperator : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) (r : ℝ) (c : 𝔤 → Fin d → E d → ℝ), ((∀ X j, ContDiffOn ℝ ∞ (c X j) (Metric.ball 0 r)) ∧ (∀ x ∈ Metric.ball (0 : E d) r, ∀ ξ : E d, ξ ≠ 0 → ∃ i, ∑ j, c (b i) j x * ξ j ≠ 0) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ X : 𝔤, ∀ x ∈ Metric.ball (0 : E d) r, h.rightDeriv X f (h.expG (coordEquiv b (x))) = ∑ j, (c X j x : ℂ) * fderiv ℝ (fun y => f (h.expG (coordEquiv b (y)))) x (ev j)) → ∀ l : List 𝔤, ∃ a : (n : ℕ) → (Fin n → Fin d) → E d → ℂ, (∀ n w, ContDiffOn ℝ ∞ (a n w) (Metric.ball 0 r)) ∧ ∀ f : G → ℂ, h.IsSmoothFun f → ∀ x ∈ Metric.ball (0 : E d) r, l.foldr h.rightDeriv f (h.expG (coordEquiv b (x))) = apOp l.length a (fun y => f (h.expG (coordEquiv b (y)))) x := by sorry
