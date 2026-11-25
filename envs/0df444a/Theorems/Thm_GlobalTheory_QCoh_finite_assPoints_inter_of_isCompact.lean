-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_finite_assPoints_inter_of_isCompact
-- name    : GlobalTheory.QCoh.finite_assPoints_inter_of_isCompact
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:41.85604+00:00
-- url     : https://prove2.me/theorems/cdcb18a7-2295-442b-aef8-ac1fea2e8add
-- title:
--   QCoh: finite ass Points inter of is Compact
-- statement:
--   The QCoh construction uses the finite ass Points inter of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L861-L869
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L861-L869

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

theorem GlobalTheory.QCoh.finite_assPoints_inter_of_isCompact [IsFiniteQC F] {K : Set X} (hK : IsCompact K) :
    (assPoints F ∩ K).Finite := by sorry
