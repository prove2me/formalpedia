-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_of_faces
-- name    : GlobalTheory.cubeComplex_exactAt_succ_of_faces
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:41.66598+00:00
-- url     : https://prove2.me/theorems/b4f0537f-e875-4e5b-b8ad-143dfdf8429c
-- title:
--   Global Theory: cube Complex exact At succ of faces
-- statement:
--   The Global Theory construction uses the cube Complex exact At succ of faces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L761-L765
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L761-L765

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
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ] {R : Type u} [Ring R]
  {e : κ ↪o ι} {i : ι} (he : Set.range e = {i}ᶜ)
include he

theorem GlobalTheory.cubeComplex_exactAt_succ_of_faces (A : Cube.{v} ι R) (p : ℕ)
    (h₀ : (cubeComplex (Cube.lowerFace e A)).ExactAt (p + 1))
    (h₁ : (cubeComplex (Cube.upperFace e i A)).ExactAt p) : (cubeComplex A).ExactAt (p + 1) := by sorry
