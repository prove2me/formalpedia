-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_resLinear
-- name    : GlobalTheory.QCoh.isLocalizedModule_resLinear
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:12.028814+00:00
-- url     : https://prove2.me/theorems/5a50c7f1-dcca-41e9-8a94-e0e52de15572
-- title:
--   QCoh: is Localized Module res Linear
-- statement:
--   The QCoh construction uses the is Localized Module res Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L296-L301

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
variable [F.IsQuasicoherent]

theorem GlobalTheory.QCoh.isLocalizedModule_resLinear (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) :
    letI := resModule F h
    IsLocalizedModule.Away f (resLinear F h) := by sorry
