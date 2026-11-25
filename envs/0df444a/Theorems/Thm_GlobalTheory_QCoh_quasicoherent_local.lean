-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_quasicoherent_local
-- name    : GlobalTheory.QCoh.quasicoherent_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:39.937797+00:00
-- url     : https://prove2.me/theorems/74e7a923-ccb9-51b4-a0de-8073c854bd64
-- title:
--   QCoh: quasicoherent local
-- statement:
--   The QCoh construction uses the quasicoherent local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L507-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L507-L522

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite TensorProduct
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}

theorem GlobalTheory.QCoh.quasicoherent_local :
    (F.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f)) ∧
    (∀ (ι : Type u) (𝒰 : ι → X.Opens), IsOpenCover 𝒰 → (∀ i, IsAffineOpen (𝒰 i)) →
      (F.IsQuasicoherent ↔
        ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f))) ∧
    (F.IsQuasicoherent → ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : V ≤ U,
      letI := resAlgebra h
      letI := resModule F h
      haveI := res_isScalarTower F h
      IsBaseChange Γ(X, V) (resLinear F h)) ∧
    (F.IsQuasicoherent → ∀ (U : X.Opens) (hU : IsAffineOpen U) (x : U),
      IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x)) := by sorry
