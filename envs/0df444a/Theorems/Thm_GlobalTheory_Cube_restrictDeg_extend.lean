-- Prove2me | Theorems.Thm_GlobalTheory_Cube_restrictDeg_extend
-- name    : GlobalTheory.Cube.restrictDeg_extend
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:41:37.838031+00:00
-- url     : https://prove2.me/theorems/29a2f46e-52b8-4515-a93c-995500953f98
-- title:
--   Cube: restrict Deg extend
-- statement:
--   The Cube construction uses the restrict Deg extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L61-L63

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

theorem GlobalTheory.Cube.restrictDeg_extend (A : Cube.{v} ι R) (p : ℕ) (x : Term A p) :
    restrictDeg A p (extend A p x) = x := by sorry
