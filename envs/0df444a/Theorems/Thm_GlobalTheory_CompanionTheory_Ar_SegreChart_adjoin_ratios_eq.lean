-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_adjoin_ratios_eq
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.adjoin_ratios_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:20:55.228242+00:00
-- url     : https://prove2.me/theorems/119f2fba-0f5f-4068-9810-02ea43f1ca52
-- title:
--   Segre Chart: adjoin ratios eq
-- statement:
--   The Segre Chart construction uses the adjoin ratios eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L182-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L182-L206

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

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.adjoin_ratios_eq (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c : (k : K ⊕ Unit) → joinIdx ι (fun _ : Unit => Fin (r + 1)) k)
    (a : Fin (N + 1)) (hEa : ∀ k, E a k = c (Sum.inl k)) (hc : ∀ k, y ⟨k, c (Sum.inl k)⟩ ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k =>
        joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩) =
      Algebra.adjoin ℚ (Set.range (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) ∪
        Set.range (fun k => x' k / x' (c (Sum.inr ())))) := by sorry
