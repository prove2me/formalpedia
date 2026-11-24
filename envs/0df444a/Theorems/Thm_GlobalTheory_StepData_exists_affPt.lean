-- Prove2me | Theorems.Thm_GlobalTheory_StepData_exists_affPt
-- name    : GlobalTheory.StepData.exists_affPt
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:14.623015+00:00
-- url     : https://prove2.me/theorems/fbf21922-bd9d-4a43-a635-bbe4b18b74b8
-- title:
--   Step Data: exists aff Pt
-- statement:
--   The Step Data construction uses the exists aff Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1192-L1196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/StandardOrderExtendedBasisApplyLowBlock.lean#L1192-L1196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type*} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n']

theorem GlobalTheory.StepData.exists_affPt {p : ℕ} {x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k}
    (h : ∀ r s, ¬ Free p (r, s) → x r s = basePt c x.toBlocks₁₁ r s) : ∃ e, affPt p x.toBlocks₁₁ e = x := by sorry
