-- Prove2me | Theorems.Thm_GlobalTheory_cechCubePushforwardIso_hom_app_apply
-- name    : GlobalTheory.cechCubePushforwardIso_hom_app_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:55.110011+00:00
-- url     : https://prove2.me/theorems/84d70700-1052-4a24-a24c-10c267c90956
-- title:
--   Global Theory: cech Cube Pushforward Iso hom app apply
-- statement:
--   The Global Theory construction uses the cech Cube Pushforward Iso hom app apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L499-L502
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/ExistsPowMulPowEqOfIsZeroCechH.lean#L499-L502

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
variable (g : Y ⟶ X) (V : X.Opens) (U : ι → X.Opens)
variable {R : Type v} [CommRing R] [Algebra R Γ(X, ⊤)] {S : Type t} [CommRing S]
  [Algebra S Γ(Y, ⊤)] {σ : R →+* S}
  {g} (hσ : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap S Γ(Y, ⊤) (σ r))
  {F : X.Modules} {G : Y.Modules} (φ : F ⟶ (Scheme.Modules.pushforward g).obj G)
variable [Algebra R Γ(Y, ⊤)]
  (hg : ∀ r, g.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(Y, ⊤) r)

theorem GlobalTheory.cechCubePushforwardIso_hom_app_apply (s : Finset ι)
    (x : sectionsOn G (g ⁻¹ᵁ cechOpen V U s)) :
    ((cechCubePushforwardIso V U G hg).hom.app s).hom x =
      sectionsOn.res R G (preimage_cechOpen g V U s).ge x := by sorry
