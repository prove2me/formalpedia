-- Prove2me | Theorems.Thm_GlobalTheory_Cube_aug_baseChange
-- name    : GlobalTheory.Cube.aug_baseChange
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:40.696617+00:00
-- url     : https://prove2.me/theorems/a1f47214-d5bd-5238-9d71-28528e654fbd
-- title:
--   Cube: aug base Change
-- statement:
--   The Cube construction uses the aug base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L904-L909
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsIsoTermComparisonRestrictScalars.lean#L904-L909

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

theorem GlobalTheory.Cube.aug_baseChange (A : Cube.{v} ι R) (x : S ⊗[R] A.obj ∅) :
    Cube.aug (Cube.baseChange S A) x = Cube.termBaseChange S A 1 ((Cube.aug A).baseChange S x) := by sorry
