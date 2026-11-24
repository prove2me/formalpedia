-- Prove2me | Theorems.Thm_GlobalTheory_AutQuotCheck_map_restrict_eq
-- name    : GlobalTheory.AutQuotCheck.map_restrict_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:54.122913+00:00
-- url     : https://prove2.me/theorems/09b9f6de-33a4-4735-98b4-eec9b735e6a6
-- title:
--   Aut Quot Check: map restrict eq
-- statement:
--   The Aut Quot Check construction uses the map restrict eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L45-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L45-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_RightInvariantOfCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.AutQuotCheck
variable {G : Type} [Group G] (Γ : Subgroup G)
open MeasureTheory
open scoped Pointwise
variable {G : Type} [Group G] (Γ : Subgroup G)

theorem GlobalTheory.AutQuotCheck.map_restrict_eq [MeasurableSpace G] [Countable Γ]
    [MeasurableConstSMul Γ G] (μ : Measure G) [SMulInvariantMeasure Γ G μ] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' μ) :
    (μ.restrict F).map (_root_.GlobalTheory.AutQuotCheck.cls Γ) =
      (μ.restrict F').map (_root_.GlobalTheory.AutQuotCheck.cls Γ) := by sorry
