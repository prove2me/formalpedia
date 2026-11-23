-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_quasiIso_faceMap
-- name    : GlobalTheory.cubeComplex_acyclic_iff_quasiIso_faceMap
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:19.925003+00:00
-- url     : https://prove2.me/theorems/cb58e13d-14ab-4c66-a33e-814f760fbd40
-- title:
--   Global Theory: cube Complex acyclic iff quasi Iso face Map
-- statement:
--   The Global Theory construction uses the cube Complex acyclic iff quasi Iso face Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L742-L759
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L742-L759

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

theorem GlobalTheory.cubeComplex_acyclic_iff_quasiIso_faceMap (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔ QuasiIso (cubeComplexMap (Cube.faceMap e i A)) := by sorry
