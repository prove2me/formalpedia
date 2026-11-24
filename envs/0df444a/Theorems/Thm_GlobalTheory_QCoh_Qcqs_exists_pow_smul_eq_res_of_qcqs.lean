-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_res_of_qcqs
-- name    : GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:15.284516+00:00
-- url     : https://prove2.me/theorems/c8b97bf2-d778-4129-8f1d-15f37aa98617
-- title:
--   Qcqs: exists pow smul eq res of qcqs
-- statement:
--   The Qcqs construction uses the exists pow smul eq res of qcqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L174-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L174-L207

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh GlobalTheory.QCoh.Qcqs
variable {X : Scheme.{u}} (F : X.Modules) {U V W : X.Opens}
variable [F.IsQuasicoherent]

theorem GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) (h : V ≤ U) (hV : V = X.basicOpen f)
    (s : Γ(F, V)) : ∃ (n : ℕ) (t : Γ(F, U)),
      X.presheaf.map (homOfLE h).op f ^ n • s = F.presheaf.map (homOfLE h).op t := by sorry
