-- Prove2me | Theorems.Thm_GlobalTheory_comap_maximalIdeal_mapIntegralClosure
-- name    : GlobalTheory.comap_maximalIdeal_mapIntegralClosure
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:10.493466+00:00
-- url     : https://prove2.me/theorems/4cdcb32a-9a92-515c-8dd8-832e8b25be09
-- title:
--   Global Theory: comap maximal Ideal map Integral Closure
-- statement:
--   The Global Theory construction uses the comap maximal Ideal map Integral Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L158-L164

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
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

theorem GlobalTheory.comap_maximalIdeal_mapIntegralClosure (σ : K →ₐ[ℚ_[p]] L) :
    (maximalIdeal (integralClosure ℤ_[p] L)).comap
        ((σ.restrictScalars ℤ_[p]).mapIntegralClosure :
          integralClosure ℤ_[p] K →+* integralClosure ℤ_[p] L) =
      maximalIdeal (integralClosure ℤ_[p] K) := by sorry
