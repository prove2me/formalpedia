-- Prove2me | Theorems.Thm_GlobalTheory_cubeComplex_acyclic_iff_exact
-- name    : GlobalTheory.cubeComplex_acyclic_iff_exact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:43:58.941055+00:00
-- url     : https://prove2.me/theorems/052e2b6a-0cdb-5118-9768-318b0a3c4411
-- title:
--   Global Theory: cube Complex acyclic iff exact
-- statement:
--   The Global Theory construction uses the cube Complex acyclic iff exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L901-L907
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L901-L907

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

theorem GlobalTheory.cubeComplex_acyclic_iff_exact (A : Cube.{v} ι R) :
    (cubeComplex A).Acyclic ↔ Function.Injective (Cube.aug A) ∧
      Function.Exact (Cube.aug A) (Cube.d A 1) ∧
        ∀ p, Function.Exact (Cube.d A (p + 1)) (Cube.d A (p + 2)) := by sorry
