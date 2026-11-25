-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_fromSpec_preimage_support
-- name    : GlobalTheory.QCoh.fromSpec_preimage_support
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:25:36.323082+00:00
-- url     : https://prove2.me/theorems/8fae70aa-6f75-4f22-ac4d-fdd50f50ece3
-- title:
--   QCoh: from Spec preimage support
-- statement:
--   The QCoh construction uses the from Spec preimage support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L455-L459
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L455-L459

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
variable (F)

theorem GlobalTheory.QCoh.fromSpec_preimage_support [F.IsQuasicoherent] (hU : IsAffineOpen U) :
    hU.fromSpec ⁻¹' support F = Module.support Γ(X, U) Γ(F, U) := by sorry
