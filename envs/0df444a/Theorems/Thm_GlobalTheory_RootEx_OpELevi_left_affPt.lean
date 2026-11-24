-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_left_affPt
-- name    : GlobalTheory.RootEx.OpELevi.left_affPt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:25:47.594834+00:00
-- url     : https://prove2.me/theorems/5b3406bd-2866-46c7-9814-e781a1114898
-- title:
--   Op ELevi: left aff Pt
-- statement:
--   The Op ELevi construction uses the left aff Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L126-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L126-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem GlobalTheory.RootEx.OpELevi.left_affPt (p : ℕ) (A : Matrix n n k) (x₀ : Matrix n n' k) (e) :
    (fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * affPt (c := c) p x₀ e
      = affPt p (A * x₀) (TL p A e) := by sorry
