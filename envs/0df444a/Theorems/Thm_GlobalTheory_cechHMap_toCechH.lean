-- Prove2me | Theorems.Thm_GlobalTheory_cechHMap_toCechH
-- name    : GlobalTheory.cechHMap_toCechH
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:11.856558+00:00
-- url     : https://prove2.me/theorems/a5e3acb3-c0ff-43e9-8ac6-58e14296303f
-- title:
--   Global Theory: cech HMap to Cech H
-- statement:
--   The Global Theory construction uses the cech HMap to Cech H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L278-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L278-L280

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoCechComplexMapPresheafCubeRes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexExactAtOfIsLocalizedModuleRes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsPowMulPowEqOfIsZeroCechH
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

theorem GlobalTheory.cechHMap_toCechH (φ : F ⟶ G) (x : sectionsOn F V) :
    (cechHMap R V U φ 0).hom (toCechH R F V U x) = toCechH R G V U (sectionsOn.map R φ V x) := by sorry
