-- Prove2me | Theorems.Thm_GlobalTheory_LevelCover_iso_cover
-- name    : GlobalTheory.LevelCover.iso_cover
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:34.848994+00:00
-- url     : https://prove2.me/theorems/27e6742b-4340-4a9f-b96d-766ae0c17f66
-- title:
--   Level Cover: iso cover
-- statement:
--   The Level Cover construction uses the iso cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean#L114-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/LevelMapFiniteEtaleSurjective.lean#L114-L165

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective
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
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l l₂ : Level H}

theorem GlobalTheory.LevelCover.iso_cover (hC : ObjCompSt) {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} (k k' : ℕ)
    {X X₂ Y : Scheme.{0}} {s : X ⟶ Sp B} {r : X₂ ⟶ X} {π : Y ⟶ X} (o : Obj D l b s) (o₂ : Obj D l₂ b₂ (r ≫ s))
    (oc : Obj D l₂ b₂ (π ≫ s)) (o₁ : Obj D l b (π ≫ s)) (n : ObjMap o₁ o π)
    (m : SABMap o₂.t o.t r) (mc : SABMap oc.t o.t π)
    (hm : (∀ a, (o₂.eta a ^ k).left ≫ m.φ = r ≫ (o.eta a).left) ∧
      (∀ a, (o₂.etaA a ^ k').left ≫ m.φ = r ≫ (o.etaA a).left))
    (hmc : (∀ a, (oc.eta a ^ k).left ≫ mc.φ = π ≫ (o.eta a).left) ∧
      (∀ a, (oc.etaA a ^ k').left ≫ mc.φ = π ≫ (o.etaA a).left))
    (hX : Represents o) (hX₂ : Represents o₂) (rX₂ : IsReduced X₂) (rY : IsReduced Y)
    (rig : ∀ m m' : SABMap o₁.t o.t π, (∀ a, ∃ σ, (o₁.eta a).left ≫ m.φ = σ ∧ (o₁.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ)
    (univ : ∀ (T : Scheme.{0}) (f : T ⟶ X) (o' : Obj D l₂ b₂ (f ≫ s)) (m' : SABMap o'.t o.t f),
      (∀ a, (o'.eta a ^ k).left ≫ m'.φ = f ≫ (o.eta a).left) ∧
        (∀ a, (o'.etaA a ^ k').left ≫ m'.φ = f ≫ (o.etaA a).left) →
      ∃! h : T ⟶ Y, h ≫ π = f ∧ ∃ u : ObjMap o' oc h, u.toSABMap.φ ≫ mc.φ = m'.φ) :
    ∃ h : X₂ ⟶ Y, IsIso h ∧ h ≫ π = r := by sorry
