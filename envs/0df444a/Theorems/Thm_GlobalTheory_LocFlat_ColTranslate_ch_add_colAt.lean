-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_ColTranslate_ch_add_colAt
-- name    : GlobalTheory.LocFlat.ColTranslate.ch_add_colAt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:32:29.717871+00:00
-- url     : https://prove2.me/theorems/2524c5fc-e571-54d2-855e-649662fa2ca8
-- title:
--   Col Translate: ch add col At
-- statement:
--   The Col Translate construction uses the ch add col At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnMapEqRootExchangeOperatorTranslate.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnMapEqRootExchangeOperatorTranslate.lean#L31-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat

theorem GlobalTheory.LocFlat.ColTranslate.ch_add_colAt {k : Type} [Field k] {n n' : Type} {c : ℕ} (p : ℕ) (y : n → k)
    (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (z + colAt n' c p y) = ch z := by sorry
