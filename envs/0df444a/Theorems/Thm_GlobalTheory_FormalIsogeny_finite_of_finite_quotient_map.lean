-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_finite_of_finite_quotient_map
-- name    : GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:04.080175+00:00
-- url     : https://prove2.me/theorems/75bb88fe-e3bb-4d3e-a9bf-e93799001df8
-- title:
--   Formal Isogeny: finite of finite quotient map
-- statement:
--   The Formal Isogeny construction uses the finite of finite quotient map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L45-L52

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

theorem GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [IsPrecomplete I A] [IsHausdorff (I.map (algebraMap A B)) B]
    [Module.Finite A (B ⧸ I.map (algebraMap A B))] : Module.Finite A B := by sorry
