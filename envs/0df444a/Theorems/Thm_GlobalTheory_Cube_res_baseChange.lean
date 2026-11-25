-- Prove2me | Theorems.Thm_GlobalTheory_Cube_res_baseChange
-- name    : GlobalTheory.Cube.res_baseChange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:56.509157+00:00
-- url     : https://prove2.me/theorems/d84926ad-46b1-4e07-942e-e70f735881b0
-- title:
--   Cube: res base Change
-- statement:
--   The Cube construction uses the res base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L865-L866
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L865-L866

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
open TensorProduct
variable {ι : Type} {R : Type u} [CommRing R]
variable (S : Type u') [CommRing S] [Algebra R S]

theorem GlobalTheory.Cube.res_baseChange (A : Cube.{v} ι R) {s t : Finset ι} (h : s ⊆ t) :
    Cube.res (Cube.baseChange S A) h = (Cube.res A h).baseChange S := by sorry
