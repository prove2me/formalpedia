-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_const_acyclic
-- name    : GlobalTheory.cubeComplex_const_acyclic
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:11.850024+00:00
-- url     : https://prove2.me/theorems/7de7ffb2-7d65-5fe8-bb79-251d67e25d18
-- title:
--   Global Theory: cube Complex const acyclic
-- statement:
--   The Global Theory construction uses the cube Complex const acyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L625-L627
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L625-L627

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

theorem GlobalTheory.cubeComplex_const_acyclic [Nonempty ι] (M : ModuleCat.{v} R) :
    (cubeComplex (Cube.const ι M)).Acyclic := by sorry
