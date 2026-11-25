-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_tfae
-- name    : GlobalTheory.QCoh.isQuasicoherent_tfae
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:03.034063+00:00
-- url     : https://prove2.me/theorems/e9d5dd32-361a-5eac-845a-89597bd17456
-- title:
--   QCoh: is Quasicoherent tfae
-- statement:
--   The QCoh construction uses the is Quasicoherent tfae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L495-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L495-L505

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

theorem GlobalTheory.QCoh.isQuasicoherent_tfae :
    List.TFAE [F.IsQuasicoherent,
      ∀ U : X.Opens, IsAffineOpen U →
        ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f),
      ∃ (ι : Type u) (𝒰 : ι → X.Opens), IsOpenCover 𝒰 ∧ (∀ i, IsAffineOpen (𝒰 i)) ∧
        ∀ i (f : Γ(X, 𝒰 i)), IsLocalizedModule.Away f (resBasicOpen F f)] := by sorry
