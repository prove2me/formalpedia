-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_mul_rowE
-- name    : GlobalTheory.RootEx.Exchange.mul_rowE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:42.106289+00:00
-- url     : https://prove2.me/theorems/3c3aa9d0-d9d0-4745-b070-768d2efbeb72
-- title:
--   Exchange: mul row E
-- statement:
--   The Exchange construction uses the mul row E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L140-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
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
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem GlobalTheory.RootEx.Exchange.mul_rowE {m : Type} (q : Fin c) (u : n → k) (x : Matrix m (n ⊕ Fin c) k) (r : m) (s : n ⊕ Fin c) :
    (x * (rowE c (q.val + 1) u).val) r s = x r s + Sum.elim (fun s' => x r (Sum.inr q) * u s') 0 s := by sorry
