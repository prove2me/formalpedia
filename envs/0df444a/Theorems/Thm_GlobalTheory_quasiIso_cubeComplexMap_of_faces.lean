-- Prove2me | Theorems.Thm_GlobalTheory_quasiIso_cubeComplexMap_of_faces
-- name    : GlobalTheory.quasiIso_cubeComplexMap_of_faces
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:50.347311+00:00
-- url     : https://prove2.me/theorems/b8d3f444-843c-4caf-876b-e770efce485b
-- title:
--   Global Theory: quasi Iso cube Complex Map of faces
-- statement:
--   The Global Theory construction uses the quasi Iso cube Complex Map of faces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L699-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L699-L703

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

theorem GlobalTheory.quasiIso_cubeComplexMap_of_faces {A B : Cube.{v} ι R} (φ : A ⟶ B)
    (h₀ : QuasiIso (cubeComplexMap (Cube.lowerFaceMap e φ)))
    (h₁ : QuasiIso (cubeComplexMap (Cube.upperFaceMap e i φ))) : QuasiIso (cubeComplexMap φ) := by sorry
