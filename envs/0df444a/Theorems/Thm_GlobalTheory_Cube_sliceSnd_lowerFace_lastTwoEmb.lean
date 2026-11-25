-- Prove2me | Theorems.Thm_GlobalTheory_Cube_sliceSnd_lowerFace_lastTwoEmb
-- name    : GlobalTheory.Cube.sliceSnd_lowerFace_lastTwoEmb
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:51.638187+00:00
-- url     : https://prove2.me/theorems/920a2332-7cd8-597b-8c2a-6b2eccd9a199
-- title:
--   Cube: slice Snd lower Face last Two Emb
-- statement:
--   The Cube construction uses the slice Snd lower Face last Two Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L921-L924
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L921-L924

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
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
open Cube
variable {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν] {R : Type u} [Ring R]

theorem GlobalTheory.Cube.sliceSnd_lowerFace_lastTwoEmb (A : Cube.{v} ((ι ⊕ₗ κ) ⊕ₗ ν) R) (t : Finset κ) :
    sliceSnd (lowerFace (lastTwoEmb ι κ ν) A) t = sliceSnd A (sumVertex ∅ t) := by sorry
