-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_segForm_weighted
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.segForm_weighted
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:21:47.398878+00:00
-- url     : https://prove2.me/theorems/0eb0f869-6435-498b-9c1d-2e2a1b6ce4cb
-- title:
--   Segre Chart: seg Form weighted
-- statement:
--   The Segre Chart construction uses the seg Form weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L35-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L35-L54

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

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.segForm_weighted {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) {Gz : MvPolynomial (Fin (N + 1)) ℤ} {n : ℕ}
    (hG : Gz.IsHomogeneous n) (w : (Σ k, ι k) → ℕ) (hw : ∀ j, ∑ k, w ⟨k, E j k⟩ = 1) :
    IsWeightedHomogeneous w (segForm E Gz) n := by sorry
