-- Prove2me | Theorems.Thm_GlobalTheory_cechHScalarsEquiv_map
-- name    : GlobalTheory.cechHScalarsEquiv_map
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:46:07.15838+00:00
-- url     : https://prove2.me/theorems/be96e9bf-bab6-4ad3-bd5d-249fa3506538
-- title:
--   Global Theory: cech HScalars Equiv map
-- statement:
--   The Global Theory construction uses the cech HScalars Equiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L402-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L402-L406

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
  (F : X.Modules) {G : X.Modules} (V : X.Opens) (U : ι → X.Opens)
variable (S : Type t) [CommRing S] [Algebra S Γ(X, ⊤)] [Algebra R S] [IsScalarTower R S Γ(X, ⊤)]
variable [LinearOrder ι]
variable {F}

theorem GlobalTheory.cechHScalarsEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechH R F V U n) :
    cechHScalarsEquiv R G V U S n ((cechHMap R V U φ n).hom x) =
      (cechHMap S V U φ n).hom (cechHScalarsEquiv R F V U S n x) := by sorry
