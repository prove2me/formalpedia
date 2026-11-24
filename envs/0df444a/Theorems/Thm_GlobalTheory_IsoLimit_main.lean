-- Prove2me | Theorems.Thm_GlobalTheory_IsoLimit_main
-- name    : GlobalTheory.IsoLimit.main
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:15.052787+00:00
-- url     : https://prove2.me/theorems/04914fe9-1023-44cd-ab80-b348e29b3baa
-- title:
--   Iso Limit: main
-- statement:
--   The Iso Limit construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersion.lean#L40-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsIsoOfIsClosedImmersion.lean#L40-L84

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

theorem GlobalTheory.IsoLimit.main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (Γ₁ Y : Over (Spec (CommRingCat.of V))) (p : Γ₁ ⟶ Y) [IsProper Y.hom] [IsProper p.left], (∀ e, IsIso ((Over.pullback (thick V (IsLocalRing.maximalIdeal V) e)).map p)) → IsIso p := by sorry
