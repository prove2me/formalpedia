-- Prove2me | Theorems.Thm_GlobalTheory_Cube_suppMap_app
-- name    : GlobalTheory.Cube.suppMap_app
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:59.916622+00:00
-- url     : https://prove2.me/theorems/b2c5d2c6-4da0-561c-b240-f56b4628adef
-- title:
--   Cube: supp Map app
-- statement:
--   The Cube construction uses the supp Map app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L134-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CubeTotalComplexAcyclicOfSlicesInductionOnCard.lean#L134-L135

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
open GlobalTheory.Cube
variable {ι : Type} {R : Type u} [Ring R]
variable {A B : Cube.{v} ι R} {P P' : Set (Finset ι)} {hP : P.OrdConnected}
  {hP' : P'.OrdConnected}

theorem GlobalTheory.Cube.suppMap_app (φ : A ⟶ B) (h) (s : Finset ι) :
    ((suppMap φ hP hP' h).app s).hom = suppMapApp φ hP hP' s := by sorry
