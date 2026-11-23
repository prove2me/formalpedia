-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_Qcqs_subsingleton_sections_of_eq_bot
-- name    : GlobalTheory.QCoh.Qcqs.subsingleton_sections_of_eq_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:14.356444+00:00
-- url     : https://prove2.me/theorems/2c8cbd54-2bec-467a-8dd1-c0faf697df15
-- title:
--   Qcqs: subsingleton sections of eq bot
-- statement:
--   The Qcqs construction uses the subsingleton sections of eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsSmulEqMapOfIsCompactOfIsQuasiSeparated.lean#L100-L103

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
variable {X : Scheme.{u}} (F : X.Modules) {V₁ V₂ W : X.Opens}

theorem GlobalTheory.QCoh.Qcqs.subsingleton_sections_of_eq_bot (h : W = ⊥) : Subsingleton Γ(F, W) := by sorry
