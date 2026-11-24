-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_OpELevi_ch_left
-- name    : GlobalTheory.RootEx.OpELevi.ch_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:25:26.111097+00:00
-- url     : https://prove2.me/theorems/22640c2d-be46-462f-a6a8-928b312afcb5
-- title:
--   Op ELevi: ch left
-- statement:
--   The Op ELevi construction uses the ch left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L162-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralCompBlocks.lean#L162-L164

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

theorem GlobalTheory.RootEx.OpELevi.ch_left (A : Matrix n n k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch ((fromBlocks A 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) * x) = ch x := by sorry
