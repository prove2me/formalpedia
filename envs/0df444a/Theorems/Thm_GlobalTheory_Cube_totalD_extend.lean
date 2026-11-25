-- Prove2me | Theorems.Thm_GlobalTheory_Cube_totalD_extend
-- name    : GlobalTheory.Cube.totalD_extend
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:37:50.626404+00:00
-- url     : https://prove2.me/theorems/a26d1873-10b0-4a80-a294-ed8294cb82e3
-- title:
--   Cube: total D extend
-- statement:
--   The Cube construction uses the total D extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L108-L120

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

theorem GlobalTheory.Cube.totalD_extend (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) :
    totalD A (extend A p x) = extend A (p + 1) (d A p x) := by sorry
