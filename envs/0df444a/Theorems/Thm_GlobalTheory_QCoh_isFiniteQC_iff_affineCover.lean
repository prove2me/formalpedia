-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isFiniteQC_iff_affineCover
-- name    : GlobalTheory.QCoh.isFiniteQC_iff_affineCover
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:27.130118+00:00
-- url     : https://prove2.me/theorems/6dfd6e79-390f-51a4-9b12-78636a78c198
-- title:
--   QCoh: is Finite QC iff affine Cover
-- statement:
--   The QCoh construction uses the is Finite QC iff affine Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L85-L90

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
attribute [instance 100] IsFiniteQC.isQuasicoherent

theorem GlobalTheory.QCoh.isFiniteQC_iff_affineCover [F.IsQuasicoherent] {ι : Type*} (𝒰 : ι → X.Opens)
    (hcov : IsOpenCover 𝒰) (haff : ∀ i, IsAffineOpen (𝒰 i)) :
    IsFiniteQC F ↔ ∀ i, Module.Finite Γ(X, 𝒰 i) Γ(F, 𝒰 i) := by sorry
