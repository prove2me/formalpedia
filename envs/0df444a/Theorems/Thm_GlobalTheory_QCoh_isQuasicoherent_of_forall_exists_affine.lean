-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_forall_exists_affine
-- name    : GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:02.782613+00:00
-- url     : https://prove2.me/theorems/2112e48a-a797-469f-9b3f-d6737399c631
-- title:
--   QCoh: is Quasicoherent of forall exists affine
-- statement:
--   The QCoh construction uses the is Quasicoherent of forall exists affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L231-L238

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

theorem GlobalTheory.QCoh.isQuasicoherent_of_forall_exists_affine
    (h : ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f)) :
    F.IsQuasicoherent := by sorry
