-- Prove2me | Theorems.Thm_GlobalTheory_hom_eq_of_thickenings_of_isProper
-- name    : GlobalTheory.hom_eq_of_thickenings_of_isProper
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:14.20637+00:00
-- url     : https://prove2.me/theorems/fa8e80c9-cc71-47f6-8a9d-1eb4e7216ce2
-- title:
--   Global Theory: hom eq of thickenings of is Proper
-- statement:
--   The Global Theory construction uses the hom eq of thickenings of is Proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersionOfThickeningsOfIsProper.lean#L59-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersionOfThickeningsOfIsProper.lean#L59-L78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIsoOfIsClosedImmersionOfThickeningsOfIsProper
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
open GlobalTheory

theorem GlobalTheory.hom_eq_of_thickenings_of_isProper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (Y Z : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] [IsSeparated Z.hom] (f g : Y ⟶ Z), (∀ e, (fstG I e Y).left ≫ f.left = (fstG I e Y).left ≫ g.left) → f = g := by sorry
