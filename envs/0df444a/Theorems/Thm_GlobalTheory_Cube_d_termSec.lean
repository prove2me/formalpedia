-- Prove2me | Theorems.Thm_GlobalTheory_Cube_d_termSec
-- name    : GlobalTheory.Cube.d_termSec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:28:05.796297+00:00
-- url     : https://prove2.me/theorems/be355e77-a5b9-4b83-a6d5-b7e3162bdc8d
-- title:
--   Cube: d term Sec
-- statement:
--   The Cube construction uses the d term Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L378-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L378-L385

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
include he

theorem GlobalTheory.Cube.d_termSec {p : ℕ} (y : Term (lowerFace e A) p) :
    d A p (termSec e i A p y) = termSec e i A (p + 1) (d (lowerFace e A) p y) +
      termIncl e i A p ((-1 : ℤ) ^ p • termMap (faceMap e i A) p y) := by sorry
