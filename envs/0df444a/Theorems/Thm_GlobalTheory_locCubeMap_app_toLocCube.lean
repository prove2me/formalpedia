-- Prove2me | Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
-- name    : GlobalTheory.locCubeMap_app_toLocCube
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:58:34.970027+00:00
-- url     : https://prove2.me/theorems/8ed09032-a61c-4a89-903d-2ca9cd8db263
-- title:
--   Global Theory: loc Cube Map app to Loc Cube
-- statement:
--   The Global Theory construction uses the loc Cube Map app to Loc Cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean#L332-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/CubeComplexExactAtOfIsLocalizedModuleRes.lean#L332-L335

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v u
open GlobalTheory
variable {ι : Type} {R : Type u} [CommRing R]
variable (f : ι → R) (M : Type v) [AddCommGroup M] [Module R M]
variable {M}

theorem GlobalTheory.locCubeMap_app_toLocCube {N : Type v} [AddCommGroup N] [Module R N] (φ : M →ₗ[R] N)
    (s : Finset ι) (m : M) :
    ((locCubeMap f φ).app s).hom (toLocCube f M s m) = toLocCube f N s (φ m) := by sorry
