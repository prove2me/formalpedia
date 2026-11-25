-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_exists_pow_le_of_finite_quotient
-- name    : GlobalTheory.FormalIsogeny.exists_pow_le_of_finite_quotient
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:08.07182+00:00
-- url     : https://prove2.me/theorems/1e8d7969-66d4-4709-9335-30927cd4f422
-- title:
--   Formal Isogeny: exists pow le of finite quotient
-- statement:
--   The Formal Isogeny construction uses the exists pow le of finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L333-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L333-L347

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
variable {R : Type*} [CommRing R] {σ τ : Type*} [Finite σ]

theorem GlobalTheory.FormalIsogeny.exists_pow_le_of_finite_quotient {k : Type*} [Field k] {J : Ideal (MvPowerSeries σ k)}
    (h : Module.Finite k (MvPowerSeries σ k ⧸ J)) : ∃ N, Ideal.span (Set.range X) ^ N ≤ J := by sorry
