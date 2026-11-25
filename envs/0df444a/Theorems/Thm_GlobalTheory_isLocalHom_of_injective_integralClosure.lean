-- Prove2me | Theorems.Thm_GlobalTheory_isLocalHom_of_injective_integralClosure
-- name    : GlobalTheory.isLocalHom_of_injective_integralClosure
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:55:49.106525+00:00
-- url     : https://prove2.me/theorems/01a36774-fe02-482d-80e2-9f0a659f34cf
-- title:
--   Global Theory: is Local Hom of injective integral Closure
-- statement:
--   The Global Theory construction uses the is Local Hom of injective integral Closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L134-L140

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
omit [Algebra ℚ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem GlobalTheory.isLocalHom_of_injective_integralClosure {B : Type*} [CommRing B] [Algebra ℤ_[p] B]
    (g : B →ₐ[ℤ_[p]] integralClosure ℤ_[p] K) (hg : Function.Injective g) :
    IsLocalHom (g : B →+* integralClosure ℤ_[p] K) := by sorry
