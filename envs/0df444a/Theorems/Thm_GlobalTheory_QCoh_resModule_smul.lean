-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_resModule_smul
-- name    : GlobalTheory.QCoh.resModule_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:52.99868+00:00
-- url     : https://prove2.me/theorems/b87ccf3b-7607-4211-9066-e314d8b53d2a
-- title:
--   QCoh: res Module smul
-- statement:
--   The QCoh construction uses the res Module smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L19-L21

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

theorem GlobalTheory.QCoh.resModule_smul (h : V ≤ U) (r : Γ(X, U)) (s : Γ(F, V)) :
    letI := resModule F h
    r • s = X.presheaf.map (homOfLE h).op r • s := by sorry
