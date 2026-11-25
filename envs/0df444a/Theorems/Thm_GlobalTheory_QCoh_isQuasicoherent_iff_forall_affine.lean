-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_forall_affine
-- name    : GlobalTheory.QCoh.isQuasicoherent_iff_forall_affine
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:48.734065+00:00
-- url     : https://prove2.me/theorems/14f3697a-d857-4dc3-bad2-a59db8795e0e
-- title:
--   QCoh: is Quasicoherent iff forall affine
-- statement:
--   The QCoh construction uses the is Quasicoherent iff forall affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L240-L247

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

theorem GlobalTheory.QCoh.isQuasicoherent_iff_forall_affine :
    F.IsQuasicoherent ↔ ∀ U : X.Opens, IsAffineOpen U →
      ∀ f : Γ(X, U), IsLocalizedModule.Away f (resBasicOpen F f) := by sorry
