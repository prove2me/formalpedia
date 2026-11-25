-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_ColTranslate_colE_neg_inv
-- name    : GlobalTheory.LocFlat.ColTranslate.colE_neg_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:32:22.999395+00:00
-- url     : https://prove2.me/theorems/782c7dbc-f2fa-576c-9821-374fdf9fe1ce
-- title:
--   Col Translate: col E neg inv
-- statement:
--   The Col Translate construction uses the col E neg inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnMapEqRootExchangeOperatorTranslate.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnMapEqRootExchangeOperatorTranslate.lean#L10-L14

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

theorem GlobalTheory.LocFlat.ColTranslate.colE_neg_inv {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (y : n → k) :
    ((colE c p (-y))⁻¹ : GL (n ⊕ Fin c) k).val = (colE c p y).val := by sorry
