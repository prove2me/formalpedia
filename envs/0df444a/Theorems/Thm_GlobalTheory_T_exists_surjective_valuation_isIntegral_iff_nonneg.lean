-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_surjective_valuation_isIntegral_iff_nonneg
-- name    : GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:50.365193+00:00
-- url     : https://prove2.me/theorems/d3fe26b8-47c9-41ef-83fa-61c6207e1efe
-- title:
--   T: exists surjective valuation is Integral iff nonneg
-- statement:
--   The T construction uses the exists surjective valuation is Integral iff nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveValuationIsIntegralIffNonnegStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveValuationIsIntegralIffNonnegStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveValuationIsIntegralIffNonneg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveValuationIsIntegralIffNonnegStatement
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

theorem GlobalTheory.T.exists_surjective_valuation_isIntegral_iff_nonneg : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.E L] [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧ ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by sorry
