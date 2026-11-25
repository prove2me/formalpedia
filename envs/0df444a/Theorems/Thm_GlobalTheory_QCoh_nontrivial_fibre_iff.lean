-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_nontrivial_fibre_iff
-- name    : GlobalTheory.QCoh.nontrivial_fibre_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:56.954515+00:00
-- url     : https://prove2.me/theorems/e53849a5-83d6-487d-8b4e-2c97c3fdb00d
-- title:
--   QCoh: nontrivial fibre iff
-- statement:
--   The QCoh construction uses the nontrivial fibre iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1125-L1127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1125-L1127

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

theorem GlobalTheory.QCoh.nontrivial_fibre_iff [IsFiniteQC F] {x : X} : Nontrivial (fibre F x) ↔ x ∈ support F := by sorry
