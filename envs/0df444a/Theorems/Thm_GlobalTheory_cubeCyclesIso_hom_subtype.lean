-- Prove2me | Theorems.Thm_GlobalTheory_cubeCyclesIso_hom_subtype
-- name    : GlobalTheory.cubeCyclesIso_hom_subtype
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:50.291596+00:00
-- url     : https://prove2.me/theorems/f4b2c3bf-a0b9-400c-87c2-434ec6261331
-- title:
--   Global Theory: cube Cycles Iso hom subtype
-- statement:
--   The Global Theory construction uses the cube Cycles Iso hom subtype property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L524-L527
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L524-L527

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cubeCyclesIso_hom_subtype (A : Cube.{v} ι R) (p : ℕ) :
    (cubeCyclesIso A p).hom ≫ ModuleCat.ofHom (LinearMap.ker (Cube.d A p)).subtype =
      (cubeComplex A).iCycles p := by sorry
