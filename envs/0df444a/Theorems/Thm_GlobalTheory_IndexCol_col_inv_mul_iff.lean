-- Prove2me | Theorems.Thm_GlobalTheory_IndexCol_col_inv_mul_iff
-- name    : GlobalTheory.IndexCol.col_inv_mul_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:33.508742+00:00
-- url     : https://prove2.me/theorems/9e8432b8-e9cb-4a1b-9577-5f25438d2d7e
-- title:
--   Index Col: col inv mul iff
-- statement:
--   The Index Col construction uses the col inv mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L21-L34

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

theorem GlobalTheory.IndexCol.col_inv_mul_iff {x : GL ι k} (hx : x ∈ KO k ι) (y : GL ι k) (t : ι) :
    (∀ s, valuation k (((x⁻¹ * y).val - 1) s t) < 1) ↔ ∀ s, valuation k ((y.val - x.val) s t) < 1 := by sorry
