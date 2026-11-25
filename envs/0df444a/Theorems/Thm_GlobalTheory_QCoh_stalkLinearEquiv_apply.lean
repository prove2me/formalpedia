-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_stalkLinearEquiv_apply
-- name    : GlobalTheory.QCoh.stalkLinearEquiv_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:38:44.735271+00:00
-- url     : https://prove2.me/theorems/1f5a198e-db03-4a95-833f-5c0635af9568
-- title:
--   QCoh: stalk Linear Equiv apply
-- statement:
--   The QCoh construction uses the stalk Linear Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L72-L73

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

theorem GlobalTheory.QCoh.stalkLinearEquiv_apply (e : F ≅ G) (x : X) (t : (F.presheaf.stalk x :)) :
    stalkLinearEquiv e x t = stalkLinear e.hom x t := by sorry

attribute [defeq] GlobalTheory.QCoh.stalkLinearEquiv_apply
