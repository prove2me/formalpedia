-- Prove2me | Theorems.Thm_GlobalTheory_FlatRed_ch_add_colAt
-- name    : GlobalTheory.FlatRed.ch_add_colAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:34:05.263295+00:00
-- url     : https://prove2.me/theorems/0ba97525-0cef-4a8f-a9da-7778fc333ffd
-- title:
--   Flat Red: ch add col At
-- statement:
--   The Flat Red construction uses the ch add col At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEqZeroOfFlatMapColumnZero.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/PartialReductionEqZeroOfFlatMapColumnZero.lean#L69-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsRead
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_PartialReductionEqZeroOfFlatMapColumnZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.FlatRed
open GlobalTheory.FlatFactor GlobalTheory.LocFlat
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {k : Type} [Field k]

theorem GlobalTheory.FlatRed.ch_add_colAt (p : ℕ) (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (y : n → k) :
    ch (z + colAt n' c p y) = ch z := by sorry
