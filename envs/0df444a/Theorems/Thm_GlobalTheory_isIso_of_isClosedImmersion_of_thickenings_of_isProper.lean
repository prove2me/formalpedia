-- Prove2me | Theorems.Thm_GlobalTheory_isIso_of_isClosedImmersion_of_thickenings_of_isProper
-- name    : GlobalTheory.isIso_of_isClosedImmersion_of_thickenings_of_isProper
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:13.261352+00:00
-- url     : https://prove2.me/theorems/a41a1c9a-a4f2-433d-9e93-d9c74be3aa23
-- title:
--   Global Theory: is Iso of is Closed Immersion of thickenings of is Proper
-- statement:
--   The Global Theory construction uses the is Iso of is Closed Immersion of thickenings of is Proper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersionOfThickeningsOfIsProper.lean#L17-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersionOfThickeningsOfIsProper.lean#L17-L57

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
open ThickeningClosed

theorem GlobalTheory.isIso_of_isClosedImmersion_of_thickenings_of_isProper {R : Type} [CommRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (Y : Over (Spec (CommRingCat.of R))) [IsProper Y.hom] {Z : Scheme.{0}} (j : Z ⟶ Y.left)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : (thickObj R I n Y).left ⟶ Z, l ≫ j = (fstG I n Y).left) : IsIso j := by sorry
