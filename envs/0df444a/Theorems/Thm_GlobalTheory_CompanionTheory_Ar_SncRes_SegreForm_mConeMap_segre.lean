-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SncRes_SegreForm_mConeMap_segre
-- name    : GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.mConeMap_segre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:38:57.716191+00:00
-- url     : https://prove2.me/theorems/53bb9bdf-911a-5113-8d21-7c8f855af227
-- title:
--   Segre Form: m Cone Map segre
-- statement:
--   The Segre Form construction uses the m Cone Map segre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StandardSmoothChartOfNonzero.lean#L119-L123

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

theorem GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm.mConeMap_segre (j : Fin (N + 1)) :
    mConeMap y (∏ k, (X ⟨k, E j k⟩ : MRing ι)) =
      (∏ k, (X k : MvPolynomial K Ω)) * C (∏ k, y ⟨k, E j k⟩) := by sorry
