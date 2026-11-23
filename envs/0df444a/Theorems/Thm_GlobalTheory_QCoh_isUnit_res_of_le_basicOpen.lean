-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isUnit_res_of_le_basicOpen
-- name    : GlobalTheory.QCoh.isUnit_res_of_le_basicOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:53.273828+00:00
-- url     : https://prove2.me/theorems/6a00247e-7fa2-4f05-922d-f60ab7a63f53
-- title:
--   QCoh: is Unit res of le basic Open
-- statement:
--   The QCoh construction uses the is Unit res of le basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L75-L78

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

theorem GlobalTheory.QCoh.isUnit_res_of_le_basicOpen (f : Γ(X, U)) (h : V ≤ U) (hV : V ≤ X.basicOpen f) :
    IsUnit (X.presheaf.map (homOfLE h).op f) := by sorry
