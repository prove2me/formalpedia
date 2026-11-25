-- Prove2me | Theorems.Thm_GlobalTheory_Cube_lowerFaceMap_app
-- name    : GlobalTheory.Cube.lowerFaceMap_app
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:46.23494+00:00
-- url     : https://prove2.me/theorems/45a7997a-fa5e-4418-b384-0e26a04e18ee
-- title:
--   Cube: lower Face Map app
-- statement:
--   The Cube construction uses the lower Face Map app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L53-L54

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

theorem GlobalTheory.Cube.lowerFaceMap_app {A B : Cube.{v} ι R} (φ : A ⟶ B) (s : Finset κ) :
    (lowerFaceMap e φ).app s = φ.app (s.map e.toEmbedding) := by sorry
