-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_iff_isBaseChange
-- name    : GlobalTheory.QCoh.isQuasicoherent_iff_isBaseChange
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:03.769667+00:00
-- url     : https://prove2.me/theorems/7ac2f1bf-02a4-5bb2-9a01-0df973d41096
-- title:
--   QCoh: is Quasicoherent iff is Base Change
-- statement:
--   The QCoh construction uses the is Quasicoherent iff is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L411-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L411-L421

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

theorem GlobalTheory.QCoh.isQuasicoherent_iff_isBaseChange :
    F.IsQuasicoherent ↔ ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → ∀ h : V ≤ U,
      letI := resAlgebra h
      letI := resModule F h
      haveI := res_isScalarTower F h
      IsBaseChange Γ(X, V) (resLinear F h) := by sorry
