-- Prove2me | Theorems.Thm_GlobalTheory_cechHMap_cechClass
-- name    : GlobalTheory.cechHMap_cechClass
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:35.667935+00:00
-- url     : https://prove2.me/theorems/1ee7f615-9f1d-4f47-ac9d-c181a2727f83
-- title:
--   Global Theory: cech HMap cech Class
-- statement:
--   The Global Theory construction uses the cech HMap cech Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L213-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L213-L217

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
import Theorems.Thm_GlobalTheory_Cube_termMap_mem_ker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe t v u
noncomputable section
open GlobalTheory
variable {X Y : Scheme.{u}} {ι : Type}
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
variable (F : X.Modules) {G H : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable [LinearOrder ι]
variable {F}

theorem GlobalTheory.cechHMap_cechClass (φ : F ⟶ G) (n : ℕ)
    (x : LinearMap.ker (Cube.d (cechCube R F V U) (n + 1))) :
    (cechHMap R V U φ n).hom (cechClass (cechCube R F V U) n x) =
      cechClass (cechCube R G V U) n ⟨_, Cube.termMap_mem_ker (cechCubeMap R V U φ) x.2⟩ := by sorry
