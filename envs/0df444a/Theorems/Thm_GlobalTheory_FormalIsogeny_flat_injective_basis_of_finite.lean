-- Prove2me | Theorems.Thm_GlobalTheory_FormalIsogeny_flat_injective_basis_of_finite
-- name    : GlobalTheory.FormalIsogeny.flat_injective_basis_of_finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:01:02.255878+00:00
-- url     : https://prove2.me/theorems/8c3ae230-7cae-4167-bd7a-f7d2fecb3072
-- title:
--   Formal Isogeny: flat injective basis of finite
-- statement:
--   The Formal Isogeny construction uses the flat injective basis of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L380-L394
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosure.lean#L380-L394

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

theorem GlobalTheory.FormalIsogeny.flat_injective_basis_of_finite {A B : Type*} [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsRegularLocalRing B] (ψ : A →+* B) [IsLocalHom ψ] (hψ : ψ.Finite)
    (hd : ringKrullDim A ≤ ringKrullDim B) :
    ψ.Flat ∧ Function.Injective ψ ∧ @Module.Free A B _ _ ψ.toAlgebra.toModule ∧
      ∃ (n : ℕ) (e : Fin n → B), ∀ g : B, ∃! c : Fin n → A, g = ∑ i, ψ (c i) * e i := by sorry
