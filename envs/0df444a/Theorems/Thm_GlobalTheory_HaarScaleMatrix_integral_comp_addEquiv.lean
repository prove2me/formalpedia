-- Prove2me | Theorems.Thm_GlobalTheory_HaarScaleMatrix_integral_comp_addEquiv
-- name    : GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:02:28.215579+00:00
-- url     : https://prove2.me/theorems/4ce47d94-9edd-4ffa-8ef2-b664f8e1b8e5
-- title:
--   Haar Scale Matrix: integral comp add Equiv
-- statement:
--   The Haar Scale Matrix construction uses the integral comp add Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureAdditiveAutomorphismScale.lean#L15-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureAdditiveAutomorphismScale.lean#L15-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRk
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureAdditiveAutomorphismScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open GlobalTheory GlobalTheory.HaarScaleMatrix

theorem GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure]
    (L : G ≃+ G) (hL : Continuous L) (hL' : Continuous L.symm) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by sorry
