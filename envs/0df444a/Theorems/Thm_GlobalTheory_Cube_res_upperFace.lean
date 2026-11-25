-- Prove2me | Theorems.Thm_GlobalTheory_Cube_res_upperFace
-- name    : GlobalTheory.Cube.res_upperFace
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:01.085551+00:00
-- url     : https://prove2.me/theorems/78d5c797-1dd7-5981-92dc-3c88e8ae60bc
-- title:
--   Cube: res upper Face
-- statement:
--   The Cube construction uses the res upper Face property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L36-L38

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

theorem GlobalTheory.Cube.res_upperFace (A : Cube.{v} ι R) {s t : Finset κ} (h : s ⊆ t) :
    res (upperFace e i A) h =
      res A (Finset.insert_subset_insert i (Finset.map_subset_map.2 h)) := by sorry
