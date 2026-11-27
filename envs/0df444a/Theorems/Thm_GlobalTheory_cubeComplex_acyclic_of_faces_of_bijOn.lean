-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_acyclic_of_faces_of_bijOn
-- name    : GlobalTheory.cubeComplex_acyclic_of_faces_of_bijOn
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:54.02343+00:00
-- url     : https://prove2.me/theorems/80e3862b-af71-4330-854b-a577b5d3507d
-- title:
--   Global Theory: cube Complex acyclic of faces of bij On
-- statement:
--   The Global Theory construction uses the cube Complex acyclic of faces of bij On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L827-L838
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L827-L838

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

theorem GlobalTheory.cubeComplex_acyclic_of_faces_of_bijOn {κ : Type} [LinearOrder κ] {e : κ ↪o ι} {i : ι}
    (he : Set.range e = {i}ᶜ) (A : Cube.{v} ι R)
    (h₀ : ∀ p, (cubeComplex (Cube.lowerFace e A)).ExactAt (p + 1))
    (h₁ : ∀ p, (cubeComplex (Cube.upperFace e i A)).ExactAt (p + 1))
    (h : Set.BijOn ((Cube.faceMap e i A).app ∅).hom
      (LinearMap.ker (Cube.aug (Cube.lowerFace e A)))
      (LinearMap.ker (Cube.aug (Cube.upperFace e i A)))) : (cubeComplex A).Acyclic := by sorry
