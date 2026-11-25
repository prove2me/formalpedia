-- Prove2me | Theorems.Thm_GlobalTheory_AutQuotCheck_normalised_eq
-- name    : GlobalTheory.AutQuotCheck.normalised_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:57:10.236734+00:00
-- url     : https://prove2.me/theorems/ece23c64-7be6-434d-a882-dca63177437e
-- title:
--   Aut Quot Check: normalised eq
-- statement:
--   The Aut Quot Check construction uses the normalised eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L94-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L94-L114

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

theorem GlobalTheory.AutQuotCheck.normalised_eq (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] {F F' : Set G}
    (h : IsFundamentalDomain Γ F μ) (h' : IsFundamentalDomain Γ F' ν) :
    (μ F)⁻¹ • (μ.restrict F).map (cls Γ) = (ν F')⁻¹ • (ν.restrict F').map (cls Γ) := by sorry
