-- Prove2me | Theorems.Thm_GlobalTheory_padic_point_comp
-- name    : GlobalTheory.padic_point_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:33.963884+00:00
-- url     : https://prove2.me/theorems/a23172ac-8cfe-589d-8c10-d5037e32a29a
-- title:
--   Global Theory: padic point comp
-- statement:
--   The Global Theory construction uses the padic point comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L366-L377
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L366-L377

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.padic_point_comp {A : Type*} [CommRing A] {K L : Type*}
    [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
    [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L] (σ : K →ₐ[ℚ_[p]] L)
    (y : A →+* integralClosure ℤ_[p] K) :
    (maximalIdeal (integralClosure ℤ_[p] L)).comap
        ((σ.restrictScalars ℤ_[p]).mapIntegralClosure.toRingHom.comp y) =
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y ∧
    RingHom.ker ((σ.restrictScalars ℤ_[p]).mapIntegralClosure.toRingHom.comp y) =
      RingHom.ker y := by sorry
