-- Prove2me | Theorems.Thm_GlobalTheory_Cube_res_lowerFace
-- name    : GlobalTheory.Cube.res_lowerFace
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:55.994942+00:00
-- url     : https://prove2.me/theorems/8fb21f85-2b58-5739-9837-f456d12a62c0
-- title:
--   Cube: res lower Face
-- statement:
--   The Cube construction uses the res lower Face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L33-L34

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

theorem GlobalTheory.Cube.res_lowerFace (A : Cube.{v} ι R) {s t : Finset κ} (h : s ⊆ t) :
    res (lowerFace e A) h = res A (Finset.map_subset_map.2 h) := by sorry
