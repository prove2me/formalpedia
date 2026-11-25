-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_primeIdealOf
-- name    : GlobalTheory.QCoh.pointOfPrime_primeIdealOf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:38:58.517176+00:00
-- url     : https://prove2.me/theorems/176c3654-ca5d-41aa-9232-70ffc105d437
-- title:
--   QCoh: point Of Prime prime Ideal Of
-- statement:
--   The QCoh construction uses the point Of Prime prime Ideal Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L118-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
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

theorem GlobalTheory.QCoh.pointOfPrime_primeIdealOf (hU : IsAffineOpen U) (x : U) :
    pointOfPrime hU (hU.primeIdealOf x) = x := by sorry
