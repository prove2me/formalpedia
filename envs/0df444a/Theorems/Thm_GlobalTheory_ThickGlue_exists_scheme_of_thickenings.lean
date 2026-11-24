-- Prove2me | Theorems.Thm_GlobalTheory_ThickGlue_exists_scheme_of_thickenings
-- name    : GlobalTheory.ThickGlue.exists_scheme_of_thickenings
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:08.300188+00:00
-- url     : https://prove2.me/theorems/fb28c834-edec-4481-82bf-b941cda5f3d1
-- title:
--   Thick Glue: exists scheme of thickenings
-- statement:
--   The Thick Glue construction uses the exists scheme of thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean#L165-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean#L165-L260

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSchemeOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickGlue
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.ThickGlue.exists_scheme_of_thickenings : ∀ (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, IsAffineOpen U) → (∀ U ∈ 𝒰, ∀ f : Γ(B₀, U), B₀.basicOpen f ∈ 𝒰) → sSup 𝒰 = ⊤ → ∀ (𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}) (π : 𝒜 ⟶ B₀.presheaf), (∀ U ∈ 𝒰, Function.Surjective (π.app (Opposite.op U)).hom ∧ IsNilpotent (RingHom.ker (π.app (Opposite.op U)).hom)) → (∀ U ∈ 𝒰, ∀ a : 𝒜.obj (Opposite.op U), letI := (𝒜.map (homOfLE (B₀.basicOpen_le ((π.app (Opposite.op U)).hom a))).op).hom.toAlgebra; IsLocalization.Away a (𝒜.obj (Opposite.op (B₀.basicOpen ((π.app (Opposite.op U)).hom a))))) → ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j) (φ : ∀ V : B.Opens, j ⁻¹ᵁ V ∈ 𝒰 → (Γ(B, V) ≅ 𝒜.obj (Opposite.op (j ⁻¹ᵁ V)))), (∀ V h, IsAffineOpen V ∧ (φ V h).hom ≫ π.app _ = j.app V) ∧ ∀ V V' h h' (hle : V' ≤ V), B.presheaf.map (homOfLE hle).op ≫ (φ V' h').hom = (φ V h).hom ≫ 𝒜.map (homOfLE (Scheme.Hom.preimage_mono j hle)).op := by sorry
