-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_SecOnR_restrict_smul
-- name    : GlobalTheory.AbLaw.SecOnR.restrict_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:49:36.673049+00:00
-- url     : https://prove2.me/theorems/ec6dd549-c2e5-48f0-b551-bdc62965f44c
-- title:
--   Sec On R: restrict smul
-- statement:
--   The Sec On R construction uses the restrict smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L462-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L462-L464

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
open GlobalTheory.AbLaw.SecOnR
variable (f : X ⟶ Spec (CommRingCat.of R)) {L M H : LB X} {V W : X.Opens}
variable {f}
variable (f)

theorem GlobalTheory.AbLaw.SecOnR.restrict_smul (h : W ≤ V) (a : Γ(X, V)) (s : SecOnR f M V) :
    restrict f M h (a • s) = rs X h a • restrict f M h s := by sorry
