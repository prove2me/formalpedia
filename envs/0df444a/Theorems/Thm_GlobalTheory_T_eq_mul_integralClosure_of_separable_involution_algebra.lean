-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_mul_integralClosure_of_separable_involution_algebra
-- name    : GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:20.544866+00:00
-- url     : https://prove2.me/theorems/a49d267b-ebd7-46cc-a22b-4fbac8fa73be
-- title:
--   T: eq mul integral Closure of separable involution algebra
-- statement:
--   The T construction uses the eq mul integral Closure of separable involution algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebra
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqMulIntegralClosureOfSeparableInvolutionAlgebraStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eq_mul_integralClosure_of_separable_involution_algebra : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ J : Submodule K.O B.A, IsLat K.O K.E J → (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) → ∃ a : B.Aˣ, J = mulLat K.O (a : B.A) (Subalgebra.toSubmodule (integralClosure K.O B.A)) := by sorry
