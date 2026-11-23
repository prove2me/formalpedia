-- Prove2me | Theorems.Thm_GlobalTheory_AutQuotCheck_measurable_cls
-- name    : GlobalTheory.AutQuotCheck.measurable_cls
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:08.151147+00:00
-- url     : https://prove2.me/theorems/2b4d9ee9-710e-4034-89ce-675a6376c9a9
-- title:
--   Aut Quot Check: measurable cls
-- statement:
--   The Aut Quot Check construction uses the measurable cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L38-L39

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

theorem GlobalTheory.AutQuotCheck.measurable_cls [MeasurableSpace G] :
    Measurable (_root_.GlobalTheory.AutQuotCheck.cls Γ) := by sorry
