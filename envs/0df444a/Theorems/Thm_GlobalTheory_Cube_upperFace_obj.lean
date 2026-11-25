-- Prove2me | Theorems.Thm_GlobalTheory_Cube_upperFace_obj
-- name    : GlobalTheory.Cube.upperFace_obj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:12.915714+00:00
-- url     : https://prove2.me/theorems/c068c105-7a0e-420f-afc3-14e40a286ceb
-- title:
--   Cube: upper Face obj
-- statement:
--   The Cube construction uses the upper Face obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L30-L31

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

theorem GlobalTheory.Cube.upperFace_obj (A : Cube.{v} ι R) (s : Finset κ) :
    (upperFace e i A).obj s = A.obj (insert i (s.map e.toEmbedding)) := by sorry
