-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point_one_lt_norm
-- name    : GlobalTheory.exists_padic_point_one_lt_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:06.551202+00:00
-- url     : https://prove2.me/theorems/144f71ed-a221-4e00-b43e-235fca6b33e6
-- title:
--   Global Theory: exists padic point one lt norm
-- statement:
--   The Global Theory construction uses the exists padic point one lt norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L116-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L116-L145

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

theorem GlobalTheory.exists_padic_point_one_lt_norm (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) {f : A} (hf : f ≠ 0) {φ : S}
    (h : ∀ s ∉ m, ∀ b : A, algebraMap A S s * φ ≠ algebraMap A S b) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
          (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 ∧
            1 < ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ :
              PadicAlgCl p)‖ := by sorry
