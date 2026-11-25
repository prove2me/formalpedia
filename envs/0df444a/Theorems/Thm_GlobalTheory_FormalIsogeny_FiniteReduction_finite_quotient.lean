-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_finite_quotient
-- name    : GlobalTheory.FormalIsogeny.FiniteReduction.finite_quotient
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:02:06.392478+00:00
-- url     : https://prove2.me/theorems/40886570-5d39-40db-9e15-833f3137f997
-- title:
--   Finite Reduction: finite quotient
-- statement:
--   The Finite Reduction construction uses the finite quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L270-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L270-L274

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

theorem GlobalTheory.FormalIsogeny.FiniteReduction.finite_quotient {f : τ → MvPowerSeries σ R} (h : FiniteReduction f) :
    Module.Finite R (MvPowerSeries σ R ⧸ Ideal.span (Set.range f)) := by sorry
