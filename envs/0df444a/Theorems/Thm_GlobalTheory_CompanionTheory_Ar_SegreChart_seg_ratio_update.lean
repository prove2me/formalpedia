-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_seg_ratio_update
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.seg_ratio_update
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:21:35.181126+00:00
-- url     : https://prove2.me/theorems/31e0999c-cec8-4166-9b5b-eb18b24ae23d
-- title:
--   Segre Chart: seg ratio update
-- statement:
--   The Segre Chart construction uses the seg ratio update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L142-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L142-L150

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
omit [∀ k, Fintype (ι k)]

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.seg_ratio_update [DecidableEq K] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c₀ : (k : K) → ι k)
    (hc : ∀ k, y ⟨k, c₀ k⟩ ≠ 0) (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c₀ k i k'⟩) / ∏ k', y ⟨k', c₀ k'⟩ = y ⟨k, i⟩ / y ⟨k, c₀ k⟩ := by sorry
