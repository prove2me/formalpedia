-- Prove2me | Theorems.Thm_GlobalTheory_Cube_upperFaceMap_app
-- name    : GlobalTheory.Cube.upperFaceMap_app
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:03:11.118077+00:00
-- url     : https://prove2.me/theorems/175a5f3c-718e-4e43-b2b5-9fdcc5843176
-- title:
--   Cube: upper Face Map app
-- statement:
--   The Cube construction uses the upper Face Map app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L56-L57

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

theorem GlobalTheory.Cube.upperFaceMap_app {A B : Cube.{v} ι R} (φ : A ⟶ B) (s : Finset κ) :
    (upperFaceMap e i φ).app s = φ.app (insert i (s.map e.toEmbedding)) := by sorry
