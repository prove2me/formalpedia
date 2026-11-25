-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_exists_homogenised
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_homogenised
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:33:00.557425+00:00
-- url     : https://prove2.me/theorems/2520cb7c-9d8a-4885-800d-ca06e7c4a945
-- title:
--   Reg: exists homogenised
-- statement:
--   The Reg construction uses the exists homogenised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L10-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L10-L88

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.exists_homogenised (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (I : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (hI : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ I) (g : MvPolynomial (Σ k, ι k) ℚ) :
    ∃ (d : ℤ) (H E : MRing ι), d ≠ 0 ∧
      mConeMap y H =
        MvPolynomial.C ((d : Ω) * aeval (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) g) * mConeMap y E ∧
      map (Int.castRingHom ℂ) H - MvPolynomial.C (d : ℂ) * map (algebraMap ℚ ℂ) g ∈ I ∧
      map (Int.castRingHom ℂ) E - 1 ∈ I := by sorry
