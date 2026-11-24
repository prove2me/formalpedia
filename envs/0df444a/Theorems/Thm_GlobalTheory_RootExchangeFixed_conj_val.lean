-- Prove2me | Theorems.Thm_GlobalTheory_RootExchangeFixed_conj_val
-- name    : GlobalTheory.RootExchangeFixed.conj_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:11.037868+00:00
-- url     : https://prove2.me/theorems/18b638de-1353-493d-8856-14cd912501d5
-- title:
--   Root Exchange Fixed: conj val
-- statement:
--   The Root Exchange Fixed construction uses the conj val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NonarchimedeanLocalFieldSecondCountableT2Space.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NonarchimedeanLocalFieldSecondCountableT2Space.lean#L15-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.RootExchangeFixed.conj_val (C : Matrix (Fin c) n k) (B : Matrix n (Fin c) k) (h : B * C = 0) :
    (lowU C * upU B * lowU (-C)).val = fromBlocks 1 B 0 (C * B + 1) := by sorry
