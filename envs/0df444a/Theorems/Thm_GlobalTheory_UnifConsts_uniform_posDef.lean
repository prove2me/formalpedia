-- Prove2me | Theorems.Thm_GlobalTheory_UnifConsts_uniform_posDef
-- name    : GlobalTheory.UnifConsts.uniform_posDef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:05.099964+00:00
-- url     : https://prove2.me/theorems/cae46d11-eec5-495c-ad1f-a474b8fa2607
-- title:
--   Unif Consts: uniform pos Def
-- statement:
--   The Unif Consts construction uses the uniform pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L37-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PeriodChartUniformConstantsHalfPolydisc.lean#L37-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PeriodChartUniformConstantsHalfPolydisc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
open GlobalTheory GlobalTheory.UnifConsts

theorem GlobalTheory.UnifConsts.uniform_posDef {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι] {K : Set X}
    (hK : IsCompact K) (F : X → Matrix ι ι ℝ) (hF : ∀ j k, ContinuousOn (fun z => F z j k) K)
    (hP : ∀ z ∈ K, (F z).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ y : ι → ℝ, c * (y ⬝ᵥ y) ≤ y ⬝ᵥ F z *ᵥ y := by sorry
