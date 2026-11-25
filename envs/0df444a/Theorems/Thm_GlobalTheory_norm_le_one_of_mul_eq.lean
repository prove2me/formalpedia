-- Prove2me | Theorems.Thm_GlobalTheory_norm_le_one_of_mul_eq
-- name    : GlobalTheory.norm_le_one_of_mul_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:17:10.049992+00:00
-- url     : https://prove2.me/theorems/95959c56-36d0-4995-a511-3d71e32dcc83
-- title:
--   Global Theory: norm le one of mul eq
-- statement:
--   The Global Theory construction uses the norm le one of mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L206-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L206-L220

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
omit [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]

theorem GlobalTheory.norm_le_one_of_mul_eq {m : Ideal A} {φ : S} {s b : A} (hs : s ∉ m)
    (hb : algebraMap A S s * φ = algebraMap A S b)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (y : A →+* integralClosure ℤ_[p] K) (hya : y a ≠ 0)
    (hy : (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m) :
    ‖(IsLocalization.Away.lift a (isUnit_val_comp_of_ne_zero y hya) φ : PadicAlgCl p)‖ ≤ 1 := by sorry
