-- Prove2me | Theorems.Thm_GlobalTheory_Cube_termUpper_d_zero
-- name    : GlobalTheory.Cube.termUpper_d_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:45.716345+00:00
-- url     : https://prove2.me/theorems/a0338c3e-e53b-4950-bb3b-b7e17f62b8bb
-- title:
--   Cube: term Upper d zero
-- statement:
--   The Cube construction uses the term Upper d zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L358-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L358-L367

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
open GlobalTheory.Cube
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι}
variable (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)

theorem GlobalTheory.Cube.termUpper_d_zero (x : Term A 0) :
    termUpper he A 0 (d A 0 x) = termMap (faceMap e i A) 0 (termLower e A 0 x) := by sorry
