-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Reg_card_le_finrank_jacSpanAt
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_finrank_jacSpanAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:41:16.377731+00:00
-- url     : https://prove2.me/theorems/3e5f4abc-9139-4a16-ab2f-8fbf9c47667e
-- title:
--   Reg: card le finrank jac Span At
-- statement:
--   The Reg construction uses the card le finrank jac Span At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L368-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SncResolutionRegularLocalRing.lean#L368-L397

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.card_le_finrank_jacSpanAt (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)) (hsnc : IsSncModel y e J)
    (p : (k : K) → ι k) (hp : ∀ k, y ⟨k, p k⟩ ≠ 0) (w : (Σ k, ι k) → ℂ)
    (hw : ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p, eval w h = 0) :
    Fintype.card (Σ k, ι k) ≤
      Module.finrank ℂ (ReciprocityTheory.AnForm.R.jacSpanAt (ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) p) w) + e := by sorry
