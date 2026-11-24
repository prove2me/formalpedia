-- Prove2me | Theorems.Thm_GlobalTheory_IndexCol_val_sum_mul_lt_one
-- name    : GlobalTheory.IndexCol.val_sum_mul_lt_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:44.023+00:00
-- url     : https://prove2.me/theorems/b612010c-e287-455e-996e-c5291d354f7c
-- title:
--   Index Col: val sum mul lt one
-- statement:
--   The Index Col construction uses the val sum mul lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndexCol
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.IndexCol.val_sum_mul_lt_one (a b : ι → k) (ha : ∀ s, a s ∈ 𝒪[k]) (hb : ∀ s, valuation k (b s) < 1) :
    valuation k (∑ s, a s * b s) < 1 := by sorry
