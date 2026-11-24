-- Prove2me | Theorems.Thm_GlobalTheory_cechAbHEquiv_map
-- name    : GlobalTheory.cechAbHEquiv_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:19:29.955455+00:00
-- url     : https://prove2.me/theorems/76322aa7-85b8-4497-a850-69dde9f52a7b
-- title:
--   Global Theory: cech Ab HEquiv map
-- statement:
--   The Global Theory construction uses the cech Ab HEquiv map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L417-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L417-L421

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

theorem GlobalTheory.cechAbHEquiv_map (φ : F ⟶ G) (n : ℕ) (x : cechAbH F.presheaf V U n) :
    cechAbHEquiv R G V U n ((cechAbHMap V U φ.mapPresheaf n).hom x) =
      (cechHMap R V U φ n).hom (cechAbHEquiv R F V U n x) := by sorry
