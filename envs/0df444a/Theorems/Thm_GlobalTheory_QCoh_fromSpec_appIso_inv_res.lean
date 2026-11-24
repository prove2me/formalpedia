-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fromSpec_appIso_inv_res
-- name    : GlobalTheory.QCoh.fromSpec_appIso_inv_res
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:47.949804+00:00
-- url     : https://prove2.me/theorems/40c2a71f-6076-4cdd-be1e-1828bfe25343
-- title:
--   QCoh: from Spec app Iso inv res
-- statement:
--   The QCoh construction uses the from Spec app Iso inv res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L111-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L111-L121

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
variable (hU : IsAffineOpen U)

theorem GlobalTheory.QCoh.fromSpec_appIso_inv_res (W : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso W).inv
      ((Spec Γ(X, U)).presheaf.map W.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
      X.presheaf.map (homOfLE (fromSpec_image_le hU W)).op r := by sorry
