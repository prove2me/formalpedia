-- Prove2me | Theorems.Thm_GlobalTheory_cechAugHomology_comp
-- name    : GlobalTheory.cechAugHomology_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:00.914358+00:00
-- url     : https://prove2.me/theorems/4a6ae200-0a4b-4e0f-a9ed-b0dadd4d847d
-- title:
--   Global Theory: cech Aug Homology comp
-- statement:
--   The Global Theory construction uses the cech Aug Homology comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L859-L863
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L859-L863

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

theorem GlobalTheory.cechAugHomology_comp (A : Cube.{v} ι R) :
    cechAugHomology A ≫ (cechHomologyZeroIso A).hom ≫
      ModuleCat.ofHom (LinearMap.ker (Cube.d A 1)).subtype = ModuleCat.ofHom (Cube.aug A) := by sorry
