-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_stalkLinear_add
-- name    : GlobalTheory.QCoh.stalkLinear_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:39:41.4491+00:00
-- url     : https://prove2.me/theorems/ee205632-e4c3-42f9-871d-0b310d0aeb8c
-- title:
--   QCoh: stalk Linear add
-- statement:
--   The QCoh construction uses the stalk Linear add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L53-L57

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

theorem GlobalTheory.QCoh.stalkLinear_add (φ ψ : F ⟶ G) (x : X) :
    stalkLinear (φ + ψ) x = stalkLinear φ x + stalkLinear ψ x := by sorry
