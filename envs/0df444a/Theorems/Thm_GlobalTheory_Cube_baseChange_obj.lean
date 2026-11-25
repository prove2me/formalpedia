-- Prove2me | Theorems.Thm_GlobalTheory_Cube_baseChange_obj
-- name    : GlobalTheory.Cube.baseChange_obj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:48.50967+00:00
-- url     : https://prove2.me/theorems/e14b0ceb-e92f-4448-a568-15d97dd01618
-- title:
--   Cube: base Change obj
-- statement:
--   The Cube construction uses the base Change obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L862-L863
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L862-L863

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

theorem GlobalTheory.Cube.baseChange_obj (A : Cube.{v} ι R) (s : Finset ι) :
    (Cube.baseChange S A).obj s = ModuleCat.of S (S ⊗[R] A.obj s) := by sorry
