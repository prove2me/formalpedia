-- Prove2me | Theorems.Thm_GlobalTheory_Cube_lowerFace_obj
-- name    : GlobalTheory.Cube.lowerFace_obj
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:57.072445+00:00
-- url     : https://prove2.me/theorems/aa258448-7e93-471a-a02c-7fc0636c77a3
-- title:
--   Cube: lower Face obj
-- statement:
--   The Cube construction uses the lower Face obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L27-L28

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
variable (e : κ ↪o ι) (i : ι)

theorem GlobalTheory.Cube.lowerFace_obj (A : Cube.{v} ι R) (s : Finset κ) :
    (lowerFace e A).obj s = A.obj (s.map e.toEmbedding) := by sorry
