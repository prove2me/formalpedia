-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point_forall_ge
-- name    : GlobalTheory.exists_padic_point_forall_ge
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:33.408321+00:00
-- url     : https://prove2.me/theorems/721c8a78-82e4-4f7a-b6f8-4a9881d7a259
-- title:
--   Global Theory: exists padic point forall ge
-- statement:
--   The Global Theory construction uses the exists padic point forall ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L379-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L379-L390

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

theorem GlobalTheory.exists_padic_point_forall_ge {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m) {f : A} (hf : f ≠ 0) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ y : A →+* integralClosure ℤ_[p] K,
          (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by sorry
