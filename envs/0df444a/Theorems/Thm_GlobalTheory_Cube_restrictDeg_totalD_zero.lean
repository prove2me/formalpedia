-- Prove2me | Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_zero
-- name    : GlobalTheory.Cube.restrictDeg_totalD_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:36:48.211583+00:00
-- url     : https://prove2.me/theorems/e322cd49-5045-4f24-bb9f-0b36f247e559
-- title:
--   Cube: restrict Deg total D zero
-- statement:
--   The Cube construction uses the restrict Deg total D zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L101-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_RangeRestrictCompSubtypeOfOrthogonalOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex TensorProduct
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
variable [LinearOrder ι]

theorem GlobalTheory.Cube.restrictDeg_totalD_zero (A : Cube.{v} ι R) (x : ∀ s, A.obj s) :
    restrictDeg A 0 (totalD A x) = 0 := by sorry
