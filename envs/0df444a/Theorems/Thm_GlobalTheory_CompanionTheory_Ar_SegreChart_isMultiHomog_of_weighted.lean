-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_isMultiHomog_of_weighted
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.isMultiHomog_of_weighted
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:20:38.8343+00:00
-- url     : https://prove2.me/theorems/cd147516-1af4-4350-894d-adf67d741005
-- title:
--   Segre Chart: is Multi Homog of weighted
-- statement:
--   The Segre Chart construction uses the is Multi Homog of weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L22-L32

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

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.isMultiHomog_of_weighted [DecidableEq K] {s : MRing ι} {n : ℕ}
    (h : ∀ k, IsWeightedHomogeneous (fun p : Σ k, ι k => if p.1 = k then 1 else 0) s n) :
    IsMultiHomog s fun _ => n := by sorry
