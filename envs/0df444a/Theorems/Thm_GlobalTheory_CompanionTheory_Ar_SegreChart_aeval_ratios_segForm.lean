-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_ratios_segForm
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_ratios_segForm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:20:54.22162+00:00
-- url     : https://prove2.me/theorems/f435dcf4-2099-4914-ac93-c219f820346b
-- title:
--   Segre Chart: aeval ratios seg Form
-- statement:
--   The Segre Chart construction uses the aeval ratios seg Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L209-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L209-L220

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
omit [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_ratios_segForm (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (c : (k : K ⊕ Unit) → joinIdx ι (fun _ : Unit => Fin (r + 1)) k)
    (a : Fin (N + 1)) (hEa : ∀ k, E a k = c (Sum.inl k)) :
    aeval (fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k => joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩)
        (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)) =
      aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz) := by sorry
