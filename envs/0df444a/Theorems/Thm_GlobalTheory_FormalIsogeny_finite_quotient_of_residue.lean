-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_finite_quotient_of_residue
-- name    : GlobalTheory.FormalIsogeny.finite_quotient_of_residue
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:43.733939+00:00
-- url     : https://prove2.me/theorems/47ef1e0d-bba9-4802-9b05-c07fa832fd47
-- title:
--   Formal Isogeny: finite quotient of residue
-- statement:
--   The Formal Isogeny construction uses the finite quotient of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L221-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L221-L263

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

theorem GlobalTheory.FormalIsogeny.finite_quotient_of_residue (J : Ideal (MvPowerSeries σ R))
    (h : Module.Finite (ResidueField R)
      (MvPowerSeries σ (ResidueField R) ⧸ J.map (MvPowerSeries.map (residue R)))) :
    Module.Finite R (MvPowerSeries σ R ⧸ J) := by sorry
