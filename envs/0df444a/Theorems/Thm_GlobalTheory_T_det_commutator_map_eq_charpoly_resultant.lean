-- Prove2me | Theorems.Thm_GlobalTheory_T_det_commutator_map_eq_charpoly_resultant
-- name    : GlobalTheory.T.det_commutator_map_eq_charpoly_resultant
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:11.226719+00:00
-- url     : https://prove2.me/theorems/b28587a3-b2e8-43e4-b4a9-76aebaf9498b
-- title:
--   T: det commutator map eq charpoly resultant
-- statement:
--   The T construction uses the det commutator map eq charpoly resultant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetCommutatorMapEqCharpolyResultantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DetCommutatorMapEqCharpolyResultantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdEApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetCommutatorMapEqCharpolyResultantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.det_commutator_map_eq_charpoly_resultant : ∀ (E : Type) [Field E] (V₁ V₂ : Type) [AddCommGroup V₁] [Module E V₁] [FiniteDimensional E V₁] [AddCommGroup V₂] [Module E V₂] [FiniteDimensional E V₂] (f₁ : V₁ →ₗ[E] V₁) (f₂ : V₂ →ₗ[E] V₂), LinearMap.det (LinearMap.llcomp E V₂ V₁ V₁ f₁ - LinearMap.lcomp E V₁ f₂) = resultant f₁.charpoly f₂.charpoly := by sorry
