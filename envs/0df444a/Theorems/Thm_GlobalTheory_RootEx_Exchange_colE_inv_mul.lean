-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Exchange_colE_inv_mul
-- name    : GlobalTheory.RootEx.Exchange.colE_inv_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:39.519066+00:00
-- url     : https://prove2.me/theorems/078cfe16-0503-45ba-b8df-961ca583c09f
-- title:
--   Exchange: col E inv mul
-- statement:
--   The Exchange construction uses the col E inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L145-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ContinuousWittExtendByZero.lean#L145-L149

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

theorem GlobalTheory.RootEx.Exchange.colE_inv_mul {m : Type} (q : Fin c) (β : n → k) (x : Matrix (n ⊕ Fin c) m k) (r : n ⊕ Fin c) (s : m) :
    (((colE c (q.val + 1) β)⁻¹ : GL (n ⊕ Fin c) k).val * x) r s =
      x r s + Sum.elim (fun r' => -(β r' * x (Sum.inr q) s)) 0 r := by sorry
