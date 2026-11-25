-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point_norm_lt
-- name    : GlobalTheory.exists_padic_point_norm_lt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:17.366292+00:00
-- url     : https://prove2.me/theorems/acb89612-9da3-4eec-9317-b18661a7e11f
-- title:
--   Global Theory: exists padic point norm lt
-- statement:
--   The Global Theory construction uses the exists padic point norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L19-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L19-L91

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

theorem GlobalTheory.exists_padic_point_norm_lt (m : Ideal A) [m.IsMaximal] (hp : (p : A) ∈ m)
    (L : Type*) [CommRing L] [Algebra A L] [IsLocalization.AtPrime L m] [IsIntegrallyClosed L]
    {b c f : A} (hc : c ≠ 0) (hf : f ≠ 0) (h : ∀ s ∉ m, ¬ c ∣ s * b) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ y : A →+* integralClosure ℤ_[p] K,
          (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 ∧
            ‖((y c : K) : PadicAlgCl p)‖ < ‖((y b : K) : PadicAlgCl p)‖ := by sorry
