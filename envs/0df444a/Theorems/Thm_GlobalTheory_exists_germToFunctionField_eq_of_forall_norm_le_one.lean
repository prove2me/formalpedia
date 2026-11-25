-- Prove2me | Theorems.Thm_GlobalTheory_exists_germToFunctionField_eq_of_forall_norm_le_one
-- name    : GlobalTheory.exists_germToFunctionField_eq_of_forall_norm_le_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:16.859646+00:00
-- url     : https://prove2.me/theorems/462cebfc-b143-4da3-b0eb-b38bb46ffe5c
-- title:
--   Global Theory: exists germ To Function Field eq of forall norm le one
-- statement:
--   The Global Theory construction uses the exists germ To Function Field eq of forall norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L431-L440
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueExtensionOfForallNormLeOne.lean#L431-L440

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

theorem GlobalTheory.exists_germToFunctionField_eq_of_forall_norm_le_one [IsNormalScheme Z] {U : Z.Opens}
    [Nonempty U] (W : Z.Opens) [Nonempty W] {φ : Γ(Z, U)}
    (h : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
      [FiniteDimensional ℚ_[p] K] (y : Spec (.of (integralClosure ℤ_[p] K)) ⟶ Z)
      (hy : ⊤ ≤ (genericPt(p, K, y)) ⁻¹ᵁ U), y (closedPoint (integralClosure ℤ_[p] K)) ∈ W →
        ‖(((Scheme.ΓSpecIso (.of K)).hom ((genericPt(p, K, y)).appLE U ⊤ hy φ) : K) :
          PadicAlgCl p)‖ ≤ 1) :
    ∃ ψ : Γ(Z, W), Z.germToFunctionField W ψ = Z.germToFunctionField U φ := by sorry
