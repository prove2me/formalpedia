-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_unique_lift
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_unique_lift
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:48.861536+00:00
-- url     : https://prove2.me/theorems/790c910b-b352-4299-94e7-9a12f3db6216
-- title:
--   Reg: exists unique lift
-- statement:
--   The Reg construction uses the exists unique lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L141-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L141-L221

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ConeChart
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_unique_lift (σ : Type) (Ω : Type) [Field Ω] [CharZero Ω] (C : Type) [CommRing C] [Algebra ℚ C]
    (u : σ → Ω) (t : σ → C) (hker : ∀ g : MvPolynomial σ ℚ, aeval u g = 0 → aeval t g = 0)
    (F : MvPolynomial σ ℚ) (hF : aeval u F ≠ 0) (hunit : IsUnit (aeval t F : C))
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (aeval u F)⁻¹ (Set.range u))) (hu : ∀ q, u q ∈ S) :
    ∃ Φ : S →ₐ[ℚ] C, (∀ q, Φ ⟨u q, hu q⟩ = t q) ∧
      ∀ Φ' : S →ₐ[ℚ] C, (∀ q, Φ' ⟨u q, hu q⟩ = t q) → Φ' = Φ := by sorry
