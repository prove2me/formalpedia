-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_exact_iff_stalkLinear
-- name    : GlobalTheory.QCoh.exact_iff_stalkLinear
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:40:08.898905+00:00
-- url     : https://prove2.me/theorems/63f368a8-577b-4836-8d83-ee1dd950bd0a
-- title:
--   QCoh: exact iff stalk Linear
-- statement:
--   The QCoh construction uses the exact iff stalk Linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L75-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsLocalizedModuleGermLinearPointOfPrime.lean#L75-L78

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

theorem GlobalTheory.QCoh.exact_iff_stalkLinear (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, Function.Exact (stalkLinear S.f x) (stalkLinear S.g x) := by sorry
