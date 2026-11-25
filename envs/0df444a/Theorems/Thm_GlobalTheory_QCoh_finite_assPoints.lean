-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_finite_assPoints
-- name    : GlobalTheory.QCoh.finite_assPoints
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:18:36.459908+00:00
-- url     : https://prove2.me/theorems/4db3f2c4-1c4c-5c69-ab89-98d4df821db5
-- title:
--   QCoh: finite ass Points
-- statement:
--   The QCoh construction uses the finite ass Points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L873-L874
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L873-L874

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
variable (F)

theorem GlobalTheory.QCoh.finite_assPoints [CompactSpace X] [IsFiniteQC F] : (assPoints F).Finite := by sorry
