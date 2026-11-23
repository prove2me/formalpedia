-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_res_res_ring
-- name    : GlobalTheory.QCoh.res_res_ring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:53.647214+00:00
-- url     : https://prove2.me/theorems/dfd29bd5-445e-4dcf-b3fb-299726c9b5a5
-- title:
--   QCoh: res res ring
-- statement:
--   The QCoh construction uses the res res ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L66-L69

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

theorem GlobalTheory.QCoh.res_res_ring (h : V ≤ U) (h' : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h').op (X.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE (h'.trans h)).op s := by sorry
