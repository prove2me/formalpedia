-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_app_res
-- name    : GlobalTheory.QCoh.Qcqs.app_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:16.805822+00:00
-- url     : https://prove2.me/theorems/3196f630-f9b0-4813-9d1c-a0f04a67966c
-- title:
--   Qcqs: app res
-- statement:
--   The Qcqs construction uses the app res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L246-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L246-L248

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
variable {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) {U V W : X.Opens}

theorem GlobalTheory.QCoh.Qcqs.app_res (h : V ≤ W) (s : Γ(F, W)) :
    φ.app V (F.presheaf.map (homOfLE h).op s) = G.presheaf.map (homOfLE h).op (φ.app W s) := by sorry
