-- Prove2me | Theorems.Thm_GlobalTheory_isIso_cechAugHomology_iff
-- name    : GlobalTheory.isIso_cechAugHomology_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:13.712579+00:00
-- url     : https://prove2.me/theorems/75a00773-3725-45ca-b548-21e0c84fefa4
-- title:
--   Global Theory: is Iso cech Aug Homology iff
-- statement:
--   The Global Theory construction uses the is Iso cech Aug Homology iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L875-L883
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexAcyclicIffQuasiIsoCechAug.lean#L875-L883

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

theorem GlobalTheory.isIso_cechAugHomology_iff (A : Cube.{v} ι R) :
    IsIso (cechAugHomology A) ↔ (cubeComplex A).ExactAt 0 ∧ (cubeComplex A).ExactAt 1 := by sorry
