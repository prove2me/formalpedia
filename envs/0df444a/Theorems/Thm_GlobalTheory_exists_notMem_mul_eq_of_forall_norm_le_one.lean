-- Prove2me | Theorems.Thm_GlobalTheory_exists_notMem_mul_eq_of_forall_norm_le_one
-- name    : GlobalTheory.exists_notMem_mul_eq_of_forall_norm_le_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:17:06.816328+00:00
-- url     : https://prove2.me/theorems/5fa982d0-a4cd-5479-a3a4-a8ff07f24126
-- title:
--   Global Theory: exists not Mem mul eq of forall norm le one
-- statement:
--   The Global Theory construction uses the exists not Mem mul eq of forall norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L147-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L147-L159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A] [IsDomain A] [CharZero A]
  [Algebra.FiniteType ℤ A]
variable {a : A} {S : Type*} [CommRing S] [Algebra A S] [IsLocalization.Away a S]

theorem GlobalTheory.exists_notMem_mul_eq_of_forall_norm_le_one (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) {φ : S}
    (h : ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
      (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
        ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1) :
    ∃ s ∉ m, ∃ b : A, algebraMap A S s * φ = algebraMap A S b := by sorry
