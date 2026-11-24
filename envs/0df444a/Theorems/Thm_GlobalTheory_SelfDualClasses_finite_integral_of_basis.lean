-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualClasses_finite_integral_of_basis
-- name    : GlobalTheory.SelfDualClasses.finite_integral_of_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:25.875239+00:00
-- url     : https://prove2.me/theorems/f4197a34-4649-430e-bf7b-f94146192f65
-- title:
--   Self Dual Classes: finite integral of basis
-- statement:
--   The Self Dual Classes construction uses the finite integral of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L44-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L44-L85

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
open GlobalTheory.SelfDualClasses
open ShortVectors

theorem GlobalTheory.SelfDualClasses.finite_integral_of_basis {n : ℕ} {ι : Type} [Fintype ι] (b : Basis ι ℚ (Fin n → E)) :
    {Λ : Submodule (𝓞 E) (Fin n → E) | (∀ i, b i ∈ Λ) ∧
      ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm 1 x y)}.Finite := by sorry
