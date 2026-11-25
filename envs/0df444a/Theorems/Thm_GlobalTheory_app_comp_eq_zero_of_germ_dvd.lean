-- Prove2me | Theorems.Thm_GlobalTheory_app_comp_eq_zero_of_germ_dvd
-- name    : GlobalTheory.app_comp_eq_zero_of_germ_dvd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T15:08:53.020886+00:00
-- url     : https://prove2.me/theorems/bb14bb39-7350-4126-a49a-16a03d05d14f
-- title:
--   Global Theory: app comp eq zero of germ dvd
-- statement:
--   The Global Theory construction uses the app comp eq zero of germ dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AppCompEqZeroOfGermDvd.lean#L20-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/AppCompEqZeroOfGermDvd.lean#L20-L33

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtIffStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecDivOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AppCompEqZeroOfGermDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.app_comp_eq_zero_of_germ_dvd {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) : ((b ≫ a).app U).hom f = 0 := by sorry
