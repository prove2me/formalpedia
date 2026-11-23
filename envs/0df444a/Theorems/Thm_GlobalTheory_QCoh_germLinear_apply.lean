-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
-- name    : GlobalTheory.QCoh.germLinear_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:38:04.883981+00:00
-- url     : https://prove2.me/theorems/f3c65fa9-e69c-46f9-b826-9539babaa716
-- title:
--   QCoh: germ Linear apply
-- statement:
--   The QCoh construction uses the germ Linear apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L449-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L449-L450

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

theorem GlobalTheory.QCoh.germLinear_apply (x : U) (s : Γ(F, U)) :
    germLinear F x s = F.presheaf.germ U x x.2 s := by sorry

attribute [defeq] GlobalTheory.QCoh.germLinear_apply
