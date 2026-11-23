-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_row_mul_rowE
-- name    : GlobalTheory.RootEx.Exchange.row_mul_rowE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:18.90584+00:00
-- url     : https://prove2.me/theorems/84dc2cfc-7d0f-4d95-b644-545caff465db
-- title:
--   Exchange: row mul row E
-- statement:
--   The Exchange construction uses the row mul row E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L282-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L282-L288

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n]

theorem GlobalTheory.RootEx.Exchange.row_mul_rowE (q : Fin c) (u : n' → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    (fun s => (affPt (q.val + 1) x₀ e * (rowE (c + 1) (q.val + 1) u).val) (Sum.inr q) (Sum.inl s)) = u := by sorry
