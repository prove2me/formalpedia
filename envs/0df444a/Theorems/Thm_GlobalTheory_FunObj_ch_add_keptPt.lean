-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_ch_add_keptPt
-- name    : GlobalTheory.FunObj.ch_add_keptPt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:09.582745+00:00
-- url     : https://prove2.me/theorems/1d49a2b2-e383-40b1-aa5f-026c50d42f21
-- title:
--   Fun Obj: ch add kept Pt
-- statement:
--   The Fun Obj construction uses the ch add kept Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L125-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}

theorem GlobalTheory.FunObj.ch_add_keptPt (z : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (w : KeptVar n c n' → k) :
    ch (z + keptPt w) = ch z := by sorry
