-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_finite_assPoints_inter_affine
-- name    : GlobalTheory.QCoh.finite_assPoints_inter_affine
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:09:42.572462+00:00
-- url     : https://prove2.me/theorems/012a4ca8-a53f-454c-8eae-7a50269ae05d
-- title:
--   QCoh: finite ass Points inter affine
-- statement:
--   The QCoh construction uses the finite ass Points inter affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L849-L857
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L849-L857

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

theorem GlobalTheory.QCoh.finite_assPoints_inter_affine [IsFiniteQC F] (hU : IsAffineOpen U) :
    (assPoints F ∩ U).Finite := by sorry
