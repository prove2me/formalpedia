-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_resLinear
-- name    : GlobalTheory.QCoh.isBaseChange_resLinear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:44.380527+00:00
-- url     : https://prove2.me/theorems/abc4aa9e-51cd-4e5a-a689-98dfed401b53
-- title:
--   QCoh: is Base Change res Linear
-- statement:
--   The QCoh construction uses the is Base Change res Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L355-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L355-L396

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

theorem GlobalTheory.QCoh.isBaseChange_resLinear [F.IsQuasicoherent] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) :
    letI := resAlgebra h
    letI := resModule F h
    haveI := res_isScalarTower F h
    IsBaseChange Γ(X, V) (resLinear F h) := by sorry
