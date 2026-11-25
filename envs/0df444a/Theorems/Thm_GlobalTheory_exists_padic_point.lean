-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point
-- name    : GlobalTheory.exists_padic_point
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:20.604782+00:00
-- url     : https://prove2.me/theorems/51ef6c19-ca56-461e-97cd-b692ae5f3667
-- title:
--   Global Theory: exists padic point
-- statement:
--   The Global Theory construction uses the exists padic point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L326-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L326-L364

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

theorem GlobalTheory.exists_padic_point {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m) {f : A} (hf : f ≠ 0) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : A →+* integralClosure ℤ_[p] K),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by sorry
