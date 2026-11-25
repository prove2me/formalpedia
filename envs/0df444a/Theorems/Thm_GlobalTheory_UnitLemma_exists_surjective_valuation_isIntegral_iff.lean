-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_exists_surjective_valuation_isIntegral_iff
-- name    : GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:08.56585+00:00
-- url     : https://prove2.me/theorems/2a616c13-e7fd-4000-9b18-259505b3238e
-- title:
--   Unit Lemma: exists surjective valuation is Integral iff
-- statement:
--   The Unit Lemma construction uses the exists surjective valuation is Integral iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveValuationIsIntegralIffNonneg.lean#L9-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsSurjectiveValuationIsIntegralIffNonneg.lean#L9-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSurjectiveValuationIsIntegralIffNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.exists_surjective_valuation_isIntegral_iff (K : UQ) (L : Type) [Field L] [Algebra K.E L]
    [Algebra K.O L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L] :
    ∃ v : Lˣ →* Multiplicative ℤ, Function.Surjective v ∧
      ∀ x : Lˣ, IsIntegral K.O (x : L) ↔ 0 ≤ Multiplicative.toAdd (v x) := by sorry
