-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_mono_iff_stalkLinear_injective
-- name    : GlobalTheory.QCoh.mono_iff_stalkLinear_injective
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:22.838559+00:00
-- url     : https://prove2.me/theorems/e0924c03-eba5-4afb-8ec3-30e0607234cb
-- title:
--   QCoh: mono iff stalk Linear injective
-- statement:
--   The QCoh construction uses the mono iff stalk Linear injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L80-L86

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

theorem GlobalTheory.QCoh.mono_iff_stalkLinear_injective (φ : F ⟶ G) :
    Mono φ ↔ ∀ x : X, Function.Injective (stalkLinear φ x) := by sorry
