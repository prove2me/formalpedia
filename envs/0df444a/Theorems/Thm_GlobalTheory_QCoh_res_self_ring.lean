-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_res_self_ring
-- name    : GlobalTheory.QCoh.res_self_ring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:42.682932+00:00
-- url     : https://prove2.me/theorems/128016ee-6ce0-4f17-9060-18529d77725c
-- title:
--   QCoh: res self ring
-- statement:
--   The QCoh construction uses the res self ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L71-L73

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

theorem GlobalTheory.QCoh.res_self_ring (h : U ≤ U) (s : Γ(X, U)) : X.presheaf.map (homOfLE h).op s = s := by sorry
