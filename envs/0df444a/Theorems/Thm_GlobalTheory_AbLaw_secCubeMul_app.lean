-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_secCubeMul_app
-- name    : GlobalTheory.AbLaw.secCubeMul_app
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:38:56.934309+00:00
-- url     : https://prove2.me/theorems/1f9a25e3-d00a-47be-aef6-fa45861bff50
-- title:
--   Ab Law: sec Cube Mul app
-- statement:
--   The Ab Law construction uses the sec Cube Mul app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L621-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/IsScalarTowerOfAlgebraMapEq.lean#L621-L622

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
variable {M}

theorem GlobalTheory.AbLaw.secCubeMul_app {H : LB X} (t : ℤ) (s : LB.Sec H) (I : Finset κ) :
    ((secCubeMul f M D t s).app I).hom = SecOnR.mulSec f M t s (⨅ i ∈ I, D i) := by sorry
