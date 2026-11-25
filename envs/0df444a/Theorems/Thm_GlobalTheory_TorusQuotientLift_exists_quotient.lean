-- Prove2me | Theorems.Thm_GlobalTheory_TorusQuotientLift_exists_quotient
-- name    : GlobalTheory.TorusQuotientLift.exists_quotient
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T16:23:49.157291+00:00
-- url     : https://prove2.me/theorems/cf712c40-f9ad-5bd4-b9b9-08d430bca7e9
-- title:
--   Torus Quotient Lift: exists quotient
-- statement:
--   The Torus Quotient Lift construction uses the exists quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorusQuotientSchemeOverNilpotentThickening.lean#L70-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTorusQuotientSchemeOverNilpotentThickening.lean#L70-L222

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGraded
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsHomOfRingMaps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KerAppEqMapAppLEOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTorusQuotientSchemeOverNilpotentThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open GlobalTheory.UU GlobalTheory.AffineThickening
noncomputable section
open GlobalTheory GlobalTheory.TorusQuotientLift
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.TorusQuotientLift.exists_quotient {A : Type} [CommRing A] {J : Ideal A} (hJ : IsNilpotent J) {G G₀ B₀ : Scheme.{0}}
    (g : G ⟶ Spec (CommRingCat.of A)) (F : G₀ ⟶ G) [IsClosedImmersion F] [Surjective F]
    (b₀ : B₀ ⟶ Spec (CommRingCat.of (A ⧸ J))) (q₀ : G₀ ⟶ B₀) (hF : F ≫ g = q₀ ≫ b₀ ≫ red J)
    (R : ∀ V : G.Opens, Subring Γ(G, V))
    (hres : ∀ (V V' : G.Opens) (h : V' ≤ V), ∀ a ∈ R V, rs h a ∈ R V')
    (hbase : ∀ V c, (g.appLE ⊤ V le_top).hom c ∈ R V)
    (hinj : ∀ U, Function.Injective (q₀.app U).hom)
    (hdesc : ∀ (U : B₀.Opens) (V : G.Opens) (e : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U), ∀ a ∈ R V,
      ∃ c, (q₀.app U).hom c = (F.appLE V _ e.ge).hom a)
    (𝒰 : Set B₀.Opens) (haff : ∀ U ∈ 𝒰, IsAffineOpen U) (hbasic : ∀ U ∈ 𝒰, ∀ f : Γ(B₀, U), B₀.basicOpen f ∈ 𝒰)
    (hcov : ∀ b : B₀, ∃ U ∈ 𝒰, b ∈ U)
    (hsurj : ∀ U ∈ 𝒰, ∀ (V : G.Opens) (e : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U) (c : Γ(B₀, U)),
      ∃ a ∈ R V, (F.appLE V _ e.ge).hom a = (q₀.app U).hom c)
    (hker : ∀ U ∈ 𝒰, ∀ (V : G.Opens) (e : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U) (a : R V), (F.appLE V _ e.ge).hom a = 0 →
      a ∈ J.map ((baseMap g V).codRestrict (R V) fun _ => hbase V _))
    (hloc : ∀ U ∈ 𝒰, ∀ (V : G.Opens) (_ : F ⁻¹ᵁ V = q₀ ⁻¹ᵁ U) (a : R V) (V' : G.Opens) (h : V' ≤ V),
      V' = G.basicOpen a.1 →
      letI := ((rs h).restrict _ _ (hres _ _ h)).toAlgebra
      IsLocalization.Away a (R V')) :
    ∃ (B : Scheme.{0}) (s : B ⟶ Spec (CommRingCat.of A)) (q : G ⟶ B) (j : B₀ ⟶ B), q ≫ s = g ∧
      IsPullback j b₀ s (red J) ∧ q₀ ≫ j = F ≫ q ∧ ∀ b : B, ∃ V : B.Opens, b ∈ V ∧ j ⁻¹ᵁ V ∈ 𝒰 ∧ IsAffineOpen V ∧
        Function.Injective (q.app V).hom ∧ ∀ a, a ∈ R (q ⁻¹ᵁ V) ↔ ∃ c, (q.app V).hom c = a := by sorry
