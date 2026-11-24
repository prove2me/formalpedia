-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_mem_conj_iff_row
-- name    : GlobalTheory.DiagVol.RowIdx.mem_conj_iff_row
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:50:22.654008+00:00
-- url     : https://prove2.me/theorems/49e73a4e-abdd-4c65-b0ee-3ac922fa72b2
-- title:
--   Row Idx: mem conj iff row
-- statement:
--   The Row Idx construction uses the mem conj iff row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L111-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L111-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruence
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
open GlobalTheory GlobalTheory.DiagVol GlobalTheory.DiagVol.RowIdx
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.DiagVol.RowIdx.mem_conj_iff_row {ϖ : kˣ} (hϖ : IsUnif ϖ) {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι}
    {S : Finset ι} (htS : t ∉ S) (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) :
    (z : GL ι k) ∈ (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom ↔
      (red (Subgroup.inclusion hHK z)).val t = (1 : Matrix ι ι 𝓀[k]) t := by sorry
