-- Prove2me | Theorems.Thm_GlobalTheory_cube_cone_of_faces
-- name    : GlobalTheory.cube_cone_of_faces
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:35.203975+00:00
-- url     : https://prove2.me/theorems/cf509dc8-682d-4dca-8068-0204e547865a
-- title:
--   Global Theory: cube cone of faces
-- statement:
--   The Global Theory construction uses the cube cone of faces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L943-L960
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L943-L960

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
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]

theorem GlobalTheory.cube_cone_of_faces {κ : Type} [LinearOrder κ] {e : κ ↪o ι} {i : ι}
    (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R) :
    (∃ hS : (ShortComplex.mk (cubeUpperIncl he A) (cubeLowerProj e A)
        (cubeFaceSequence he A).zero).ShortExact,
      (∀ p, Nonempty ((cubeFaceSequence he A).map (eval _ _ p)).Splitting) ∧
      ∀ p, hS.δ p (p + 1) rfl ≫
          (shiftSuccHomologyIso (cubeComplex (Cube.upperFace e i A)) p).hom =
        (-1 : ℤ) ^ p • homologyMap (cubeComplexMap (Cube.faceMap e i A)) p) ∧
    ((∀ s : Finset ι, i ∉ s → Function.Bijective (Cube.res A (Finset.subset_insert i s))) →
      (cubeComplex A).Acyclic) ∧
    (∀ (B : Cube.{v} ι R) (φ : A ⟶ B), QuasiIso (cubeComplexMap (Cube.lowerFaceMap e φ)) →
      QuasiIso (cubeComplexMap (Cube.upperFaceMap e i φ)) → QuasiIso (cubeComplexMap φ)) ∧
    ((cubeComplex A).Acyclic ↔
      IsIso (cechAugHomology A) ∧ ∀ p, IsZero ((cechComplex A).homology (p + 1))) := by sorry
