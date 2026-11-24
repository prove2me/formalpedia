-- Prove2me | Theorems.Thm_GlobalTheory_IsoLimit_isIso_of_isClosedImmersion
-- name    : GlobalTheory.IsoLimit.isIso_of_isClosedImmersion
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:21:39.963368+00:00
-- url     : https://prove2.me/theorems/202c97db-5834-425d-bf4d-90a163b3a008
-- title:
--   Iso Limit: is Iso of is Closed Immersion
-- statement:
--   The Iso Limit construction uses the is Iso of is Closed Immersion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersion.lean#L17-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersion.lean#L17-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsIsoOfIsClosedImmersion
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
open GlobalTheory GlobalTheory.IsoLimit
open ThickeningClosed

theorem GlobalTheory.IsoLimit.isIso_of_isClosedImmersion {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    {X Z : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of V)) [IsProper f] (j : Z ⟶ X)
    [IsClosedImmersion j]
    (h : ∀ n : ℕ, ∃ l : pullback f (thick V (IsLocalRing.maximalIdeal V) n) ⟶ Z,
      l ≫ j = pullback.fst f (thick V (IsLocalRing.maximalIdeal V) n)) : IsIso j := by sorry
