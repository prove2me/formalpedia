-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_aeval_blockRatio_mem
-- name    : GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.aeval_blockRatio_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:39:27.064467+00:00
-- url     : https://prove2.me/theorems/fcd8e673-0b9b-5147-8b76-3e6928f2036e
-- title:
--   Segre Form: aeval block Ratio mem
-- statement:
--   The Segre Form construction uses the aeval block Ratio mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L99-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L99-L109

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

theorem GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.aeval_blockRatio_mem [CharZero Ω] (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (β : MRing ι) :
    aeval (fun p : Σ k, ι k => y p / y ⟨p.1, E c₀ p.1⟩) β ∈
      Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) := by sorry
