-- Prove2me | Theorems.Thm_GlobalTheory_AutQuotCheck_cls_smul
-- name    : GlobalTheory.AutQuotCheck.cls_smul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:58:10.141067+00:00
-- url     : https://prove2.me/theorems/372ccdef-0d35-4c8a-b084-07aac9fa80b1
-- title:
--   Aut Quot Check: cls smul
-- statement:
--   The Aut Quot Check construction uses the cls smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/RightInvariantOfCovolume.lean#L29-L33

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

theorem GlobalTheory.AutQuotCheck.cls_smul (γ : Γ) (x : G) :
    _root_.GlobalTheory.AutQuotCheck.cls Γ (γ • x) = _root_.GlobalTheory.AutQuotCheck.cls Γ x := by sorry
