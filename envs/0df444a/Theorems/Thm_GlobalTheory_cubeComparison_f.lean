-- Prove2me | Theorems.Thm_GlobalTheory_cubeComparison_f
-- name    : GlobalTheory.cubeComparison_f
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:53.972241+00:00
-- url     : https://prove2.me/theorems/ae30d1f1-6362-4733-82c0-4ef6cc976cc2
-- title:
--   Global Theory: cube Comparison f
-- statement:
--   The Global Theory construction uses the cube Comparison f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L743-L744
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L743-L744

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
variable {ι : Type} {R : Type u} [Ring R] {S : Type u'} [Ring S]
  (F : ModuleCat.{v} R ⥤ ModuleCat.{v'} S)
variable [LinearOrder ι] [F.Additive]

theorem GlobalTheory.cubeComparison_f (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComparison F A).f p = Cube.termComparison F A p := by sorry
