-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_segForm
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_segForm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:12.359802+00:00
-- url     : https://prove2.me/theorems/c356c322-5f25-424c-b924-a3abbf08ba76
-- title:
--   Segre Chart: aeval seg Form
-- statement:
--   The Segre Chart construction uses the aeval seg Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L16-L20

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

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_segForm {R : Type} [CommRing R] (v : (Σ k, ι k) → R) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (Gz : MvPolynomial (Fin (N + 1)) ℤ) :
    aeval v (segForm E Gz) = aeval (fun j => ∏ k, v ⟨k, E j k⟩) Gz := by sorry
