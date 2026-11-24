-- Prove2me | Theorems.Thm_GlobalTheory_ThickGlue_isClosedImmersion_toSpec
-- name    : GlobalTheory.ThickGlue.isClosedImmersion_toSpec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:07:55.611174+00:00
-- url     : https://prove2.me/theorems/a135bbbe-4fea-4b94-9e4c-f2d64ab0f24e
-- title:
--   Thick Glue: is Closed Immersion to Spec
-- statement:
--   The Thick Glue construction uses the is Closed Immersion to Spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean#L139-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSchemeOfThickenings.lean#L139-L144

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

theorem GlobalTheory.ThickGlue.isClosedImmersion_toSpec {B₀ : Scheme.{0}} {𝒜 : B₀.Opensᵒᵖ ⥤ CommRingCat.{0}}
    (p : 𝒜 ⟶ B₀.presheaf) {U : B₀.Opens} (hU : IsAffineOpen U)
    (h : Function.Surjective (p.app (Opposite.op U)).hom) : IsClosedImmersion (toSpec p U) := by sorry
