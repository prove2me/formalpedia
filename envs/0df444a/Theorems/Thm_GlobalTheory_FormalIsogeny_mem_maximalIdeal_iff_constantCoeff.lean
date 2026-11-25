-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_mem_maximalIdeal_iff_constantCoeff
-- name    : GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:51.065014+00:00
-- url     : https://prove2.me/theorems/1ee723c8-e9fe-48cd-b0fa-21e72b806347
-- title:
--   Formal Isogeny: mem maximal Ideal iff constant Coeff
-- statement:
--   The Formal Isogeny construction uses the mem maximal Ideal iff constant Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L143-L146

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

theorem GlobalTheory.FormalIsogeny.mem_maximalIdeal_iff_constantCoeff [IsLocalRing R] {g : MvPowerSeries σ R} :
    g ∈ maximalIdeal (MvPowerSeries σ R) ↔ constantCoeff g ∈ maximalIdeal R := by sorry
