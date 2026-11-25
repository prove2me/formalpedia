-- Prove2me | Theorems.Thm_GlobalTheory_Cube_restrictDeg_totalD_succ
-- name    : GlobalTheory.Cube.restrictDeg_totalD_succ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:48.66672+00:00
-- url     : https://prove2.me/theorems/184d3258-3d28-5bff-a946-28399bcef75c
-- title:
--   Cube: restrict Deg total D succ
-- statement:
--   The Cube construction uses the restrict Deg total D succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/RangeRestrictCompSubtypeOfOrthogonalOfNe.lean#L97-L99

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

theorem GlobalTheory.Cube.restrictDeg_totalD_succ (A : Cube.{v} ι R) (p : ℕ) (x : ∀ s, A.obj s) :
    restrictDeg A (p + 1) (totalD A x) = d A p (restrictDeg A p x) := by sorry
