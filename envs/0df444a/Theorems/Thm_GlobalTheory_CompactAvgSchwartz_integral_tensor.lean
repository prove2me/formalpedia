-- Prove2me | Theorems.Thm_GlobalTheory_CompactAvgSchwartz_integral_tensor
-- name    : GlobalTheory.CompactAvgSchwartz.integral_tensor
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:01:00.107876+00:00
-- url     : https://prove2.me/theorems/3e167d43-f2c9-49ac-892b-7bc07d687c99
-- title:
--   Compact Avg Schwartz: integral tensor
-- statement:
--   The Compact Avg Schwartz construction uses the integral tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L191-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchwartzIntegral.lean#L191-L235

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchwartzIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.CompactAvgSchwartz

theorem GlobalTheory.CompactAvgSchwartz.integral_tensor {S V Y : Type} [TopologicalSpace S] [CompactSpace S] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace S] [OpensMeasurableSpace S] [TopologicalSpace Y] (ν : Measure S)
    [IsFiniteMeasure ν] (L Li : S → V →L[ℝ] V) (hL : Continuous L) (hLi : Continuous Li) (h : ∀ s x, Li s (L s x) = x)
    (a b : S → Y → Y) (ha : Continuous fun p : S × Y => a p.1 p.2) (hb : Continuous fun p : S × Y => b p.1 p.2)
    (hab : ∀ s y, b s (a s y) = y) (f : SchwartzMap V ℂ) {g : Y → ℂ} (hg : g ∈ WeilM.SB Y) :
    (∀ x y, Integrable (fun s => f (L s x) * g (a s y)) ν) ∧
    ∃ (t : Finset (Y → ℂ)) (F : (Y → ℂ) → SchwartzMap V ℂ), (∀ g' ∈ t, g' ∈ WeilM.SB Y) ∧
      ∀ x y, ∫ s, f (L s x) * g (a s y) ∂ν = ∑ g' ∈ t, F g' x * g' y := by sorry
