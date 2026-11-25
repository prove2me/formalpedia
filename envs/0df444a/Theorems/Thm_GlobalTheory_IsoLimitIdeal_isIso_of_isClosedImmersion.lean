-- Prove2me | Theorems.Thm_GlobalTheory_IsoLimitIdeal_isIso_of_isClosedImmersion
-- name    : GlobalTheory.IsoLimitIdeal.isIso_of_isClosedImmersion
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:00:52.956704+00:00
-- url     : https://prove2.me/theorems/72f69194-d518-45b8-8488-7709246228b9
-- title:
--   Iso Limit Ideal: is Iso of is Closed Immersion
-- statement:
--   The Iso Limit Ideal construction uses the is Iso of is Closed Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsClosedImmersion.lean#L18-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsIsoOfIsClosedImmersion.lean#L18-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsIsoOfIsClosedImmersion
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
open GlobalTheory GlobalTheory.IsoLimitIdeal
open ThickeningClosed

theorem GlobalTheory.IsoLimitIdeal.isIso_of_isClosedImmersion {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (I : Ideal V) (hI : I ≠ ⊤) {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V I n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V I n)) : IsIso j := by sorry
