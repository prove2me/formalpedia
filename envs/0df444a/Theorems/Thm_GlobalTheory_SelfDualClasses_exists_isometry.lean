-- Prove2me | Theorems.Thm_GlobalTheory_SelfDualClasses_exists_isometry
-- name    : GlobalTheory.SelfDualClasses.exists_isometry
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:51:57.090503+00:00
-- url     : https://prove2.me/theorems/34a02cbc-8e35-49e7-8dec-71a28445c0e3
-- title:
--   Self Dual Classes: exists isometry
-- statement:
--   The Self Dual Classes construction uses the exists isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L25-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/FiniteClassesSelfDualOfSelfDual.lean#L25-L42

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

theorem GlobalTheory.SelfDualClasses.exists_isometry {n : ℕ} {ι : Type} (b b' : Basis ι ℚ (Fin n → E))
    (h : ∀ i j, herm 1 (b' i) (b' j) = herm 1 (b i) (b j)) :
    ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), (∀ x y, herm 1 (γ x) (γ y) = herm 1 x y) ∧
      ∀ i, γ (b i) = b' i := by sorry
