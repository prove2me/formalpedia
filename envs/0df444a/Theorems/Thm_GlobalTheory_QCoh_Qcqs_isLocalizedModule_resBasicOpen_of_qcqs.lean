-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_isLocalizedModule_resBasicOpen_of_qcqs
-- name    : GlobalTheory.QCoh.Qcqs.isLocalizedModule_resBasicOpen_of_qcqs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:56.3818+00:00
-- url     : https://prove2.me/theorems/c559290b-8b4f-4258-8f5a-ba626a23a780
-- title:
--   Qcqs: is Localized Module res Basic Open of qcqs
-- statement:
--   The Qcqs construction uses the is Localized Module res Basic Open of qcqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L209-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L209-L214

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

theorem GlobalTheory.QCoh.Qcqs.isLocalizedModule_resBasicOpen_of_qcqs (hU : IsCompact (U : Set X))
    (hU' : IsQuasiSeparated (U : Set X)) (f : Γ(X, U)) :
    IsLocalizedModule.Away f (resBasicOpen F f) := by sorry
