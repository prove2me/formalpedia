-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_exactAt_succ_iff_faces
-- name    : GlobalTheory.cubeComplex_exactAt_succ_iff_faces
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:38.292257+00:00
-- url     : https://prove2.me/theorems/ebd2fb24-2d4e-47f8-9017-49ab6ff48426
-- title:
--   Global Theory: cube Complex exact At succ iff faces
-- statement:
--   The Global Theory construction uses the cube Complex exact At succ iff faces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L732-L740
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L732-L740

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

theorem GlobalTheory.cubeComplex_exactAt_succ_iff_faces (A : Cube.{v} ι R) (p : ℕ) :
    (cubeComplex A).ExactAt (p + 1) ↔
      Epi (homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) ∧
        Mono (homologyMap (cubeComplexMap (Cube.faceMap e i A)) (p + 1)) := by sorry
