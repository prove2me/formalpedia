-- Prove2me | Theorems.Thm_GlobalTheory_ThickGlue_exists_glue
-- name    : GlobalTheory.ThickGlue.exists_glue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:21.123464+00:00
-- url     : https://prove2.me/theorems/452f2b2a-3672-43bd-a572-b07d5112acd8
-- title:
--   Thick Glue: exists glue
-- statement:
--   The Thick Glue construction uses the exists glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean#L15-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean#L15-L117

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

theorem GlobalTheory.ThickGlue.exists_glue (B₀ : Scheme.{0}) (𝒰 : Set B₀.Opens)
    (hbas : ∀ U ∈ 𝒰, ∀ (W : B₀.Opens) (x : B₀), x ∈ U → x ∈ W → ∃ V ∈ 𝒰, x ∈ V ∧ V ≤ U ∧ V ≤ W)
    (hcov : sSup 𝒰 = ⊤) (F : 𝒰 ⥤ Scheme.{0})
    (hF : ∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f))
    (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U)
    (he : ∀ U, IsClosedImmersion (e U)) (hs : ∀ U, Surjective (e U))
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ (B : Scheme.{0}) (j : B₀ ⟶ B) (_ : IsClosedImmersion j) (_ : Surjective j)
      (κ : ∀ U, F.obj U ⟶ B) (_ : ∀ U, IsOpenImmersion (κ U)),
      (∀ U, U.1.ι ≫ j = e U ≫ κ U) ∧ (∀ U, j ⁻¹ᵁ (κ U).opensRange = U.1) ∧
      ∀ {U V : 𝒰} (f : U ⟶ V), F.map f ≫ κ V = κ U := by sorry
