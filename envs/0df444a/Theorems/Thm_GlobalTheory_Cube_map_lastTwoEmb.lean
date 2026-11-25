-- Prove2me | Theorems.Thm_GlobalTheory_Cube_map_lastTwoEmb
-- name    : GlobalTheory.Cube.map_lastTwoEmb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:06:04.743368+00:00
-- url     : https://prove2.me/theorems/f0ad4447-70ac-5f8b-99c8-1338c3217620
-- title:
--   Cube: map last Two Emb
-- statement:
--   The Cube construction uses the map last Two Emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L916-L919
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L916-L919

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

theorem GlobalTheory.Cube.map_lastTwoEmb (t : Finset κ) (w : Finset ν) :
    (sumVertex t w).map (lastTwoEmb ι κ ν).toEmbedding =
      sumVertex (sumVertex (∅ : Finset ι) t) w := by sorry
