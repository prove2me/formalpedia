-- Prove2me | Theorems.Thm_GlobalTheory_SectionsDescent_coord_mul_rs
-- name    : GlobalTheory.SectionsDescent.coord_mul_rs
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:35.129591+00:00
-- url     : https://prove2.me/theorems/4de0fbdc-387e-4016-82a1-18f9186498d2
-- title:
--   Sections Descent: coord mul rs
-- statement:
--   The Sections Descent construction uses the coord mul rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L101-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/IsExtensionAffine.lean#L101-L113

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionPullOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SectionsDescent
open GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F] {Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of K)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom (algebraMap K F))))

theorem GlobalTheory.SectionsDescent.coord_mul_rs {V W : Y.Opens} (hV : IsAffineOpen V) (h : W ≤ V) {ℓ : F →ₗ[K] K}
    {Λ : FnOver π' (p ⁻¹ᵁ V) →+ FnOver π V} {Λ' : FnOver π' (p ⁻¹ᵁ W) →+ FnOver π W}
    (hΛ : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ V))) ℓ Λ) (hΛ' : IsCoord (pullFn H.w (le_refl (p ⁻¹ᵁ W))) ℓ Λ')
    (u : Γ(Y, W)) (x : Γ(Y', p ⁻¹ᵁ V)) :
    Λ' ((p.app W).hom u * rs (pre_mono p h) x) = u * rs h (Λ x) := by sorry
