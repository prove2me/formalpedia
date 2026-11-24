-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isBaseChange_germLinear
-- name    : GlobalTheory.QCoh.isBaseChange_germLinear
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:57:58.320237+00:00
-- url     : https://prove2.me/theorems/1c8b3790-2cbf-4750-b43c-03d71bde1904
-- title:
--   QCoh: is Base Change germ Linear
-- statement:
--   The QCoh construction uses the is Base Change germ Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L487-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L487-L491

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

theorem GlobalTheory.QCoh.isBaseChange_germLinear [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsBaseChange (X.presheaf.stalk (x : X)) (germLinear F x) := by sorry
