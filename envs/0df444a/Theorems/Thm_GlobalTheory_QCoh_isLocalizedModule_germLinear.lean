-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear
-- name    : GlobalTheory.QCoh.isLocalizedModule_germLinear
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:52.404413+00:00
-- url     : https://prove2.me/theorems/d3868df2-ed98-46a9-af8b-13ba4e03e949
-- title:
--   QCoh: is Localized Module germ Linear
-- statement:
--   The QCoh construction uses the is Localized Module germ Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L459-L485
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsQuasicoherentOfForallExistsAffine.lean#L459-L485

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

theorem GlobalTheory.QCoh.isLocalizedModule_germLinear [F.IsQuasicoherent] (hU : IsAffineOpen U) (x : U) :
    IsLocalizedModule (hU.primeIdealOf x).asIdeal.primeCompl (germLinear F x) := by sorry
