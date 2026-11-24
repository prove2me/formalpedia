-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_relIndex_rowCong
-- name    : GlobalTheory.DiagVol.RowIdx.relIndex_rowCong
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:38.990822+00:00
-- url     : https://prove2.me/theorems/44646352-4452-4bda-8b0b-6a60a0406d92
-- title:
--   Row Idx: rel Index row Cong
-- statement:
--   The Row Idx construction uses the rel Index row Cong property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L149-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L149-L210

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

theorem GlobalTheory.DiagVol.RowIdx.relIndex_rowCong : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) →
    (∀ y : ι → k, (∀ s, y s ∈ 𝒪[k]) → (∀ s, s ∉ S → y s = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0)) →
    ((KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom).relIndex H = resCard k ^ S.card := by sorry
