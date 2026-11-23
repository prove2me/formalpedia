-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_inv_mul_affPt
-- name    : GlobalTheory.RootEx.Exchange.colE_inv_mul_affPt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:44.619016+00:00
-- url     : https://prove2.me/theorems/58a38221-cf9a-4466-8685-d7f449e640d0
-- title:
--   Exchange: col E inv mul aff Pt
-- statement:
--   The Exchange construction uses the col E inv mul aff Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L200-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L200-L222

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
omit [Fintype n']

theorem GlobalTheory.RootEx.Exchange.colE_inv_mul_affPt (q : Fin c) (β : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    ((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * affPt (q.val + 1) x₀ e =
      mat x₀ (ext0 (Free (q.val + 1)) (e + sCol q β e) + gCol q (-β)) := by sorry
