-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_evC_rename_inl
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.evC_rename_inl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:21:11.68789+00:00
-- url     : https://prove2.me/theorems/9b3d76a6-2d2c-44cf-a74d-3d142f34ad91
-- title:
--   Segre Chart: ev C rename inl
-- statement:
--   The Segre Chart construction uses the ev C rename inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L126-L129

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
variable {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K₂] [∀ k, Fintype (ι₂ k)]

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.evC_rename_inl (z : (Σ k, joinIdx ι ι₂ k) → ℂ) (g : MRing ι) :
    evC z (rename (joinInl ι ι₂) g) = evC (fun p => z (joinInl ι ι₂ p)) g := by sorry
