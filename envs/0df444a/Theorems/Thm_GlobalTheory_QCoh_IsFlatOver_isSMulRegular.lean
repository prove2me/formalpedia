-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_IsFlatOver_isSMulRegular
-- name    : GlobalTheory.QCoh.IsFlatOver.isSMulRegular
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:24:07.139798+00:00
-- url     : https://prove2.me/theorems/285e69e4-4ce3-4628-bb07-4a3d45f5f066
-- title:
--   Is Flat Over: is SMul Regular
-- statement:
--   The Is Flat Over construction uses the is SMul Regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1326-L1336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/TopologicalKrullDimLeOfIrreducibleCloseds.lean#L1326-L1336

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
variable {R : Type*} [CommRing R] (ρ : R →+* Γ(X, ⊤))
variable {ρ}

theorem GlobalTheory.QCoh.IsFlatOver.isSMulRegular (h : IsFlatOver F ρ) {r : R} (hr : r ∈ nonZeroDivisors R)
    (U : X.Opens) : IsSMulRegular Γ(F, U) (baseHom U ρ r) := by sorry
