-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_rename_inl_mem
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.rename_inl_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:21:57.796142+00:00
-- url     : https://prove2.me/theorems/bd2ac2cd-ef3a-442a-9e92-aa667fbfaede
-- title:
--   Segre Chart: rename inl mem
-- statement:
--   The Segre Chart construction uses the rename inl mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L108-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L108-L123

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

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.rename_inl_mem {Ω : Type} [Field Ω] (y₁ : (Σ k, ι k) → Ω) (y₂ : (Σ k, ι₂ k) → Ω) {f : MRing ι}
    (hf : f ∈ mCoordIdeal y₁) : rename (joinInl ι ι₂) f ∈ mCoordIdeal (joinVec y₁ y₂) := by sorry
