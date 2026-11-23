-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mem_primeCompl_primeIdealOf_iff
-- name    : GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:59.926561+00:00
-- url     : https://prove2.me/theorems/8f946597-1dd1-4688-a4da-eec96b4f192c
-- title:
--   QCoh: mem prime Compl prime Ideal Of iff
-- statement:
--   The QCoh construction uses the mem prime Compl prime Ideal Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L452-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L452-L457

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

theorem GlobalTheory.QCoh.mem_primeCompl_primeIdealOf_iff (hU : IsAffineOpen U) (x : U) (f : Γ(X, U)) :
    f ∈ (hU.primeIdealOf x).asIdeal.primeCompl ↔ (x : X) ∈ X.basicOpen f := by sorry
