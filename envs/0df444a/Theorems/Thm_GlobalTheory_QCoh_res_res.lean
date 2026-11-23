-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_res_res
-- name    : GlobalTheory.QCoh.res_res
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:35.747137+00:00
-- url     : https://prove2.me/theorems/95b09243-b11a-4055-92cf-26ba3b2b6a7e
-- title:
--   QCoh: res res
-- statement:
--   The QCoh construction uses the res res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L57-L60

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

theorem GlobalTheory.QCoh.res_res (h : V ≤ U) (h' : W ≤ V) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE h').op (F.presheaf.map (homOfLE h).op s) =
      F.presheaf.map (homOfLE (h'.trans h)).op s := by sorry
