-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_blockFnField_joinPt
-- name    : GlobalTheory.CompanionTheory.Ar.SegreChart.blockFnField_joinPt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:21:16.25771+00:00
-- url     : https://prove2.me/theorems/b2764681-51ff-46dc-a017-c95634fd5187
-- title:
--   Segre Chart: block Fn Field join Pt
-- statement:
--   The Segre Chart construction uses the block Fn Field join Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L160-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/HomogeneousFormNonvanishingPoint.lean#L160-L178

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

theorem GlobalTheory.CompanionTheory.Ar.SegreChart.blockFnField_joinPt (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω)
    (hF : ∀ i l, x' l ≠ 0 → x' i / x' l ∈ blockFnField y) :
    blockFnField (joinPt y x') = blockFnField y := by sorry
