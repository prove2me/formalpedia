-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_isAdicComplete_maximalIdeal_of_finite
-- name    : GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:51.234358+00:00
-- url     : https://prove2.me/theorems/3d56656f-0807-4f94-bfa4-0b9505e8cd71
-- title:
--   Formal Isogeny: is Adic Complete maximal Ideal of finite
-- statement:
--   The Formal Isogeny construction uses the is Adic Complete maximal Ideal of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L65-L77

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

theorem GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by sorry
