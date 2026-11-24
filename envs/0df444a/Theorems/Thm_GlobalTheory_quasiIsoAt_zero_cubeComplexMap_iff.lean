-- Prove2me | Theorems.Thm_GlobalTheory_quasiIsoAt_zero_cubeComplexMap_iff
-- name    : GlobalTheory.quasiIsoAt_zero_cubeComplexMap_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:14:42.142822+00:00
-- url     : https://prove2.me/theorems/499ef9b6-3288-41f3-a2db-c44cf9f32746
-- title:
--   Global Theory: quasi Iso At zero cube Complex Map iff
-- statement:
--   The Global Theory construction uses the quasi Iso At zero cube Complex Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L779-L825
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L779-L825

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

theorem GlobalTheory.quasiIsoAt_zero_cubeComplexMap_iff {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    QuasiIsoAt (cubeComplexMap φ) 0 ↔ Set.BijOn (φ.app ∅).hom
      (LinearMap.ker (Cube.aug A)) (LinearMap.ker (Cube.aug B)) := by sorry
