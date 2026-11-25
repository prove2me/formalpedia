-- Prove2me | Theorems.Thm_GlobalTheory_exists_padic_point_scheme_one_lt_norm
-- name    : GlobalTheory.exists_padic_point_scheme_one_lt_norm
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:18:06.818514+00:00
-- url     : https://prove2.me/theorems/0604e6e1-9763-54c3-b075-3f51567ce95e
-- title:
--   Global Theory: exists padic point scheme one lt norm
-- statement:
--   The Global Theory construction uses the exists padic point scheme one lt norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L317-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L317-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueExtensionOfForallNormLeOne
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
local notation "genericPt(" p ", " K ", " y ")" =>
  Spec.map (CommRingCat.ofHom (algebraMap (integralClosure ℤ_[p] K) K)) ≫ y
variable {Z : Scheme.{0}} [IsIntegral Z] (π : Z ⟶ Spec (.of ℤ)) [Flat π] [LocallyOfFiniteType π]
include π

theorem GlobalTheory.exists_padic_point_scheme_one_lt_norm {p : ℕ} [Fact p.Prime] {x : Z}
    (hx : IsClosed ({x} : Set Z)) (hp : (p : Z.residueField x) = 0)
    [IsIntegrallyClosed (Z.presheaf.stalk x)] {U : Z.Opens} [Nonempty U] (U' : Z.Opens)
    [Nonempty U'] {φ : Γ(Z, U)}
    (h : Z.germToFunctionField U φ ∉ (algebraMap (Z.presheaf.stalk x) Z.functionField).range) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K], K₀ ≤ K →
        ∃ (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z) (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U),
          y (closedPoint (integralClosure ℤ_[p] K)) = x ∧ y (genericPoint _) ∈ U' ∧
            1 < ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
              PadicAlgCl p)‖ := by sorry
