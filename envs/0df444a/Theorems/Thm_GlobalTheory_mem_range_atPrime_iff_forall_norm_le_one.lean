-- Prove2me | Theorems.Thm_GlobalTheory_mem_range_atPrime_iff_forall_norm_le_one
-- name    : GlobalTheory.mem_range_atPrime_iff_forall_norm_le_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:11:49.650114+00:00
-- url     : https://prove2.me/theorems/2be742c4-9abd-4bd0-a0c2-6a936fc13f95
-- title:
--   Global Theory: mem range at Prime iff forall norm le one
-- statement:
--   The Global Theory construction uses the mem range at Prime iff forall norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L222-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L222-L234

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

theorem GlobalTheory.mem_range_atPrime_iff_forall_norm_le_one (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    (ha : a ≠ 0) (F : Type*) [Field F] [Algebra A F] [FaithfulSMul A F] [Algebra S F]
    [Algebra L F] [IsScalarTower A S F] [IsScalarTower A L F] (φ : S) :
    algebraMap S F φ ∈ (algebraMap L F).range ↔
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
        (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0),
        (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m →
          ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ :
            PadicAlgCl p)‖ ≤ 1 := by sorry
