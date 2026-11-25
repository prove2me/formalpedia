-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_of_forall_norm_le_one
-- name    : GlobalTheory.mem_range_of_forall_norm_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:16:57.830506+00:00
-- url     : https://prove2.me/theorems/1d6b65a3-7b79-5867-aa62-f3b76da9e84b
-- title:
--   Global Theory: mem range of forall norm le one
-- statement:
--   The Global Theory construction uses the mem range of forall norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L236-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L236-L255

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

theorem GlobalTheory.mem_range_of_forall_norm_le_one [IsIntegrallyClosed A] (ha : a ≠ 0) {φ : S}
    (h : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K] (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
        ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1) :
    φ ∈ (algebraMap A S).range := by sorry
