-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_vanish_of_value
-- name    : GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.vanish_of_value
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:40:28.791235+00:00
-- url     : https://prove2.me/theorems/03623dc0-7571-5520-b922-308e99048798
-- title:
--   Segre Form: vanish of value
-- statement:
--   The Segre Form construction uses the vanish of value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L125-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L125-L176

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_FiniteEtaleSurjectiveOfPullback
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StandardSmoothChartOfNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncRes GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {N : ℕ} (y : (Σ k, ι k) → Ω) (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))

theorem GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.vanish_of_value (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {β : MRing ι} {b : K → ℕ} (hb : IsMultiHomog β b)
    {n : ℕ} {m : ℤ} {G : MvPolynomial (Fin (N + 1)) ℤ} (hG : G.IsHomogeneous n)
    (hval : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) G =
      (m : Ω) * aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hβ : evC z β = 0) :
    (∏ k, z ⟨k, E c₀ k⟩) = 0 ∨ aeval (fun j => ∏ k, z ⟨k, E j k⟩) G = 0 := by sorry
