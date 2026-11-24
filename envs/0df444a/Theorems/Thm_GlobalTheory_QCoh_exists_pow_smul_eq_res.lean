-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exists_pow_smul_eq_res
-- name    : GlobalTheory.QCoh.exists_pow_smul_eq_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:52.205006+00:00
-- url     : https://prove2.me/theorems/e37b1e62-c131-47f8-b3f3-786bd05ac34a
-- title:
--   QCoh: exists pow smul eq res
-- statement:
--   The QCoh construction uses the exists pow smul eq res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L283-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L283-L288

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

theorem GlobalTheory.QCoh.exists_pow_smul_eq_res (hU : IsAffineOpen U) (f : Γ(X, U)) (h : V ≤ U)
    (hV : V = X.basicOpen f) (s : Γ(F, V)) :
    ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by sorry
