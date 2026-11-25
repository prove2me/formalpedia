-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_pointOfPrime_mem_assPoints_iff
-- name    : GlobalTheory.QCoh.pointOfPrime_mem_assPoints_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:17.669812+00:00
-- url     : https://prove2.me/theorems/72cc3b93-cba4-4824-9f5a-176ad1c00bcd
-- title:
--   QCoh: point Of Prime mem ass Points iff
-- statement:
--   The QCoh construction uses the point Of Prime mem ass Points iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L842-L845
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L842-L845

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

theorem GlobalTheory.QCoh.pointOfPrime_mem_assPoints_iff [F.IsQuasicoherent] (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) :
    (pointOfPrime hU P : X) ∈ assPoints F ↔ P.asIdeal ∈ associatedPrimes Γ(X, U) Γ(F, U) := by sorry
