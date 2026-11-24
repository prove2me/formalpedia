-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_zero
-- name    : GlobalTheory.QCoh.exists_pow_smul_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:46.910158+00:00
-- url     : https://prove2.me/theorems/a3d2d2a4-c576-4887-b04a-d39c44be63ae
-- title:
--   QCoh: exists pow smul eq zero
-- statement:
--   The QCoh construction uses the exists pow smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L290-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L290-L294

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

theorem GlobalTheory.QCoh.exists_pow_smul_eq_zero (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) (t : Γ(F, U)) (ht : F.presheaf.map (homOfLE h).op t = 0) :
    ∃ n : ℕ, f ^ n • t = 0 := by sorry
