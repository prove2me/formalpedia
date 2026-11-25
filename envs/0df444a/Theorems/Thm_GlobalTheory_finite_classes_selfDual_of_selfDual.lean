-- Prove2me | Theorems.Thm_GlobalTheory_finite_classes_selfDual_of_selfDual
-- name    : GlobalTheory.finite_classes_selfDual_of_selfDual
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:07.151716+00:00
-- url     : https://prove2.me/theorems/d3f37d0a-3249-4004-a5b2-d53fa5c5eefe
-- title:
--   Global Theory: finite classes self Dual of self Dual
-- statement:
--   The Global Theory construction uses the finite classes self Dual of self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L111-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L111-L165

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open SelfDualClasses

theorem GlobalTheory.finite_classes_selfDual_of_selfDual (n : ℕ) :
    ∃ S : Finset (Submodule (𝓞 E) (Fin n → E)),
    (∀ Λ ∈ S, Λ.FG ∧ (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) ∧
      ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) ∧
    ∀ Λ : Submodule (𝓞 E) (Fin n → E), Λ.FG →
    (∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) →
    (∀ x, (∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)) → x ∈ Λ) →
    ∃ Λ₀ ∈ S, ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E),
      (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧ ∀ x, x ∈ Λ₀ ↔ γ x ∈ Λ := by sorry
