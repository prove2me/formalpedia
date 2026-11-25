-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_res_secCube
-- name    : GlobalTheory.AbLaw.res_secCube
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:37:26.664149+00:00
-- url     : https://prove2.me/theorems/e3801ee0-625a-409d-a72b-9109c1e02ed7
-- title:
--   Ab Law: res sec Cube
-- statement:
--   The Ab Law construction uses the res sec Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L570-L571
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L570-L571

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
variable {κ : Type} (f : X ⟶ Spec (CommRingCat.of R)) {L : LB X} (M : LB X) (D : κ → X.Opens)

theorem GlobalTheory.AbLaw.res_secCube {s t : Finset κ} (h : s ⊆ t) :
    GlobalTheory.Cube.res (secCube f M D) h = SecOnR.restrict f M (iInf_le_iInf_of_subset D h) := by sorry
