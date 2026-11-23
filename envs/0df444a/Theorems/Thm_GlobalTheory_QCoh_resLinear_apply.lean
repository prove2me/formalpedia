-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- name    : GlobalTheory.QCoh.resLinear_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:32.384822+00:00
-- url     : https://prove2.me/theorems/1b0a6537-3a3a-45b0-a214-86228b280111
-- title:
--   QCoh: res Linear apply
-- statement:
--   The QCoh construction uses the res Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L40-L41

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

theorem GlobalTheory.QCoh.resLinear_apply (h : V ≤ U) (s : Γ(F, U)) :
    resLinear F h s = F.presheaf.map (homOfLE h).op s := by sorry

attribute [defeq] GlobalTheory.QCoh.resLinear_apply
