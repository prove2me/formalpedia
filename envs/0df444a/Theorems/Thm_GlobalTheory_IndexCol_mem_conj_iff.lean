-- Prove2me | Theorems.Thm_GlobalTheory_IndexCol_mem_conj_iff
-- name    : GlobalTheory.IndexCol.mem_conj_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:15:38.573803+00:00
-- url     : https://prove2.me/theorems/210b91cd-14f1-42b3-8076-59a39bdf2953
-- title:
--   Index Col: mem conj iff
-- statement:
--   The Index Col construction uses the mem conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L78-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L78-L93

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

theorem GlobalTheory.IndexCol.mem_conj_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) {z : GL ι k} (hz : z ∈ KO k ι) :
    z ∈ (KO k ι).map (MulAut.conj ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹)).toMonoidHom ↔
      (∀ r, r ≠ t → valuation k (z.val r t) < 1) ∧ ∀ r, r ≠ t → valuation k ((z⁻¹).val r t) < 1 := by sorry
