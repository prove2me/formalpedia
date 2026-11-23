-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
-- name    : GlobalTheory.QCoh.resBasicOpen_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:39.639806+00:00
-- url     : https://prove2.me/theorems/7d4ec4aa-35a8-4dfb-b9a7-e649c2e36d0e
-- title:
--   QCoh: res Basic Open apply
-- statement:
--   The QCoh construction uses the res Basic Open apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L54-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L54-L55

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

theorem GlobalTheory.QCoh.resBasicOpen_apply (f : Γ(X, U)) (s : Γ(F, U)) :
    resBasicOpen F f s = F.presheaf.map (homOfLE (X.basicOpen_le f)).op s := by sorry

attribute [defeq] GlobalTheory.QCoh.resBasicOpen_apply
