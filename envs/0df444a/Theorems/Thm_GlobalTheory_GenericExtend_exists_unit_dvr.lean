-- Prove2me | Theorems.Thm_GlobalTheory_GenericExtend_exists_unit_dvr
-- name    : GlobalTheory.GenericExtend.exists_unit_dvr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T01:01:12.871163+00:00
-- url     : https://prove2.me/theorems/e332c196-9d6f-4716-a67a-0e7ea97158f9
-- title:
--   Generic Extend: exists unit dvr
-- statement:
--   The Generic Extend construction uses the exists unit dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L223-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLineBundleGeneratorExtendingDensePart.lean#L223-L260

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleGeneratorExtendingDensePart
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenericExtend

theorem GlobalTheory.GenericExtend.exists_unit_dvr {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] {X P Q H Z : Scheme.{0}}
    {f : H ⟶ Spec (.of V)} [Smooth f] [GeometricallyIntegral f] {k : Z ⟶ H} {fK : Z ⟶ Spec (.of K)}
    (hK : IsPullback k fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    {N : LB P} (hN : N.IsLB) {J : Q ⟶ P} {φ : H ⟶ P} {ψ : Z ⟶ Q} (hψ : ψ ≫ J = k ≫ φ)
    (hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A)
    {e : X ⟶ P} {l : Spec (.of V) ⟶ X} {eV : Spec (.of V) ⟶ H} (heV : eV ≫ φ = l ≫ e)
    (heV' : eV ≫ f = 𝟙 _) {eK : Spec (.of K) ⟶ Z}
    (heK : eK ≫ k = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ eV)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ z a, e (l (Spec.map (CommRingCat.ofHom (algebraMap V K)) z)) ∈ N.U a →
      gm (eK ≫ ψ) z (J ⁻¹ᵁ N.U a) (τ a) =
        gm (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ s : Γ(H, φ ⁻¹ᵁ N.U a)ˣ, res le_rfl (pullU k _ s) = res (hW _) (pullU ψ _ (τ a)) := by sorry
