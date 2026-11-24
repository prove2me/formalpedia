-- Prove2me | Theorems.Thm_GlobalTheory_FlatThickenings_flat_chart
-- name    : GlobalTheory.FlatThickenings.flat_chart
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:08.25762+00:00
-- url     : https://prove2.me/theorems/bebc9d2f-7f5b-4f9b-93a9-2bb6ec7f7d9b
-- title:
--   Flat Thickenings: flat chart
-- statement:
--   The Flat Thickenings construction uses the flat chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MemPowOfFlatQuotient.lean#L84-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MemPowOfFlatQuotient.lean#L84-L107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MemPowOfFlatQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatThickenings

theorem GlobalTheory.FlatThickenings.flat_chart {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {B : Scheme.{0}} (f : B ⟶ Spec (CommRingCat.of V)) [LocallyOfFiniteType f]
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
    (b : ∀ e, (Y e).left ⟶ B)
    (hb : ∀ e, IsPullback (b e) (Y e).hom f (thick V (IsLocalRing.maximalIdeal V) e))
    (hY : ∀ e, Flat (Y e).hom) {C : CommRingCat.{0}} (u : Spec C ⟶ B) [IsOpenImmersion u] :
    Flat (u ≫ f) := by sorry
