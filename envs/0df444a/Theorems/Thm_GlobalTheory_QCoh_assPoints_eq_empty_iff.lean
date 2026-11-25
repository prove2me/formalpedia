-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_assPoints_eq_empty_iff
-- name    : GlobalTheory.QCoh.assPoints_eq_empty_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:53.089956+00:00
-- url     : https://prove2.me/theorems/bd9a6cc4-c68c-59fa-879a-2820c191a39c
-- title:
--   QCoh: ass Points eq empty iff
-- statement:
--   The QCoh construction uses the ass Points eq empty iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L908-L913
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L908-L913

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
variable [IsLocallyNoetherian X]

theorem GlobalTheory.QCoh.assPoints_eq_empty_iff [F.IsQuasicoherent] : assPoints F = ∅ ↔ IsZero F := by sorry
