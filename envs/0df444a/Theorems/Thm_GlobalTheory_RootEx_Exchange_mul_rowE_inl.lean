-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_mul_rowE_inl
-- name    : GlobalTheory.RootEx.Exchange.mul_rowE_inl
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:24:12.978124+00:00
-- url     : https://prove2.me/theorems/91143a63-2476-4ecd-be13-ab88a25644cb
-- title:
--   Exchange: mul row E inl
-- statement:
--   The Exchange construction uses the mul row E inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableOfMemSB.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegrableOfMemSB.lean#L30-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Exchange
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.RootEx.Exchange.mul_rowE_inl (P : Fin c) (u : n → k) (M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (r) (s : n) :
    (M * (rowE c (P.val + 1) u).val) r (Sum.inl s) = M r (Sum.inl s) + M r (Sum.inr P) * u s := by sorry
