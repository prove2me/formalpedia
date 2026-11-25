-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_ringKrullDim_mvPowerSeries
-- name    : GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:54.65865+00:00
-- url     : https://prove2.me/theorems/1b321e8c-677e-4a9a-9eec-b401505f7ff7
-- title:
--   Formal Isogeny: ring Krull Dim mv Power Series
-- statement:
--   The Formal Isogeny construction uses the ring Krull Dim mv Power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L210-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L210-L217

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

theorem GlobalTheory.FormalIsogeny.ringKrullDim_mvPowerSeries (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (σ : Type*) [Finite σ] : ringKrullDim (MvPowerSeries σ R) = ringKrullDim R + Nat.card σ := by sorry
