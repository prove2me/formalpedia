-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_isLocalHom_of_constantCoeff_mem
-- name    : GlobalTheory.FormalIsogeny.isLocalHom_of_constantCoeff_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:08.085607+00:00
-- url     : https://prove2.me/theorems/01d1f1cb-a630-4407-aae0-9fd0c6c86550
-- title:
--   Formal Isogeny: is Local Hom of constant Coeff mem
-- statement:
--   The Formal Isogeny construction uses the is Local Hom of constant Coeff mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L304-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L304-L312

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasSubstEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open GlobalTheory GlobalTheory.FormalIsogeny
variable {R : Type*} [CommRing R] {σ τ : Type*}
variable [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]
variable [Finite τ]
omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Finite σ]

theorem GlobalTheory.FormalIsogeny.isLocalHom_of_constantCoeff_mem (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) : IsLocalHom φ.toRingHom := by sorry
