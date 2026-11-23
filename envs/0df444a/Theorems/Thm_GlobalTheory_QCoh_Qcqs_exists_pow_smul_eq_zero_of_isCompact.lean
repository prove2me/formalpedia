-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_exists_pow_smul_eq_zero_of_isCompact
-- name    : GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:30.768799+00:00
-- url     : https://prove2.me/theorems/61c5a671-2ae6-4736-acd6-ae6b2a0e0cb8
-- title:
--   Qcqs: exists pow smul eq zero of is Compact
-- statement:
--   The Qcqs construction uses the exists pow smul eq zero of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L150-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L150-L172

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

theorem GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (h : V ≤ U) (hV : V = X.basicOpen f) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE h).op t = 0) : ∃ n : ℕ, f ^ n • t = 0 := by sorry
