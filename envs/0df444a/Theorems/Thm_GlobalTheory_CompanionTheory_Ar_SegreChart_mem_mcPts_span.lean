-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_mem_mcPts_span
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.mem_mcPts_span
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:21:31.831048+00:00
-- url     : https://prove2.me/theorems/b5cbd440-b0a9-4770-baac-5ad82a53b782
-- title:
--   Segre Chart: mem mc Pts span
-- statement:
--   The Segre Chart construction uses the mem mc Pts span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L273-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L273-L297

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.mem_mcPts_span (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) (β : MRing ι) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0)
    (z : (Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal (joinPt y x')))
    (hb : evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0) :
    z ∈ mcPts (Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}) := by sorry
