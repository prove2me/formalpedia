-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_flat_injective_basis_of_finiteReduction
-- name    : GlobalTheory.FormalIsogeny.flat_injective_basis_of_finiteReduction
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:03:16.141979+00:00
-- url     : https://prove2.me/theorems/9128c736-1086-4507-b6ca-117844a2443f
-- title:
--   Formal Isogeny: flat injective basis of finite Reduction
-- statement:
--   The Formal Isogeny construction uses the flat injective basis of finite Reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L396-L408
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L396-L408

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
variable {R : Type*} [CommRing R] [IsRegularLocalRing R] [IsAdicComplete (maximalIdeal R) R]
  {σ τ : Type*} [Finite σ] [Finite τ]

theorem GlobalTheory.FormalIsogeny.flat_injective_basis_of_finiteReduction (φ : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R)
    (h0 : ∀ j, constantCoeff (φ (X j)) ∈ maximalIdeal R) (h : FiniteReduction fun j => φ (X j))
    (hc : Nat.card τ ≤ Nat.card σ) :
    φ.toRingHom.Flat ∧ Function.Injective φ ∧
      @Module.Free (MvPowerSeries τ R) (MvPowerSeries σ R) _ _ φ.toRingHom.toAlgebra.toModule ∧
      ∃ (n : ℕ) (e : Fin n → MvPowerSeries σ R),
        ∀ g, ∃! c : Fin n → MvPowerSeries τ R, g = ∑ i, φ (c i) * e i := by sorry
