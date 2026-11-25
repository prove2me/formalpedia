-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_coord_secOnRTrivEquiv
-- name    : GlobalTheory.AbLaw.coord_secOnRTrivEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:38:04.491524+00:00
-- url     : https://prove2.me/theorems/140fff62-ba20-4cf0-aca3-b1aae92d7c7d
-- title:
--   Ab Law: coord sec On RTriv Equiv
-- statement:
--   The Ab Law construction uses the coord sec On RTriv Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L664-L672
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L664-L672

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem GlobalTheory.AbLaw.coord_secOnRTrivEquiv (f : X ⟶ Spec (CommRingCat.of R)) [IsIso f] {V : X.Opens}
    (hV : V = ⊤) (r : R) (i : (Inh.trivLB X).ι) :
    SecOnR.coord (secOnRTrivEquiv f hV r) i = cst f _ r := by sorry
