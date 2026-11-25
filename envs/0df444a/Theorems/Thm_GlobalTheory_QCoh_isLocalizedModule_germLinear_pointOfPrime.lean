-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isLocalizedModule_germLinear_pointOfPrime
-- name    : GlobalTheory.QCoh.isLocalizedModule_germLinear_pointOfPrime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:57:39.771347+00:00
-- url     : https://prove2.me/theorems/98f63a8e-b5a7-4f95-869f-c36e899a4ae6
-- title:
--   QCoh: is Localized Module germ Linear point Of Prime
-- statement:
--   The QCoh construction uses the is Localized Module germ Linear point Of Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L122-L127

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

theorem GlobalTheory.QCoh.isLocalizedModule_germLinear_pointOfPrime (F : X.Modules) [F.IsQuasicoherent]
    (hU : IsAffineOpen U) (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
    IsLocalizedModule P.primeCompl (germLinear F (pointOfPrime hU ⟨P, hP⟩)) := by sorry
