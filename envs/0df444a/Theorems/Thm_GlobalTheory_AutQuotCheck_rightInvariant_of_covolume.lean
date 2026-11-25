-- Prove2me | Theorems.Thm_GlobalTheory_AutQuotCheck_rightInvariant_of_covolume
-- name    : GlobalTheory.AutQuotCheck.rightInvariant_of_covolume
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:35.878985+00:00
-- url     : https://prove2.me/theorems/e83ea378-994c-451a-b730-33b5f75331d9
-- title:
--   Aut Quot Check: right Invariant of covolume
-- statement:
--   The Aut Quot Check construction uses the right Invariant of covolume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L77-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L77-L92

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]
open MeasureTheory
open scoped Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [Countable Γ]

theorem GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (μ : Measure G) [μ.IsHaarMeasure] {F : Set G}
    (h : IsFundamentalDomain Γ F μ) (h0 : μ F ≠ 0) (h1 : μ F ≠ ⊤) (g : G) :
    μ.map (· * g) = μ := by sorry
