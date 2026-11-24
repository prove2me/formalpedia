-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_conj_diag_val
-- name    : GlobalTheory.DiagVol.RowIdx.conj_diag_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:30.835384+00:00
-- url     : https://prove2.me/theorems/864befbb-fb2a-4f5f-8a43-2b041ef5338c
-- title:
--   Row Idx: conj diag val
-- statement:
--   The Row Idx construction uses the conj diag val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L67-L72

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.DiagVol.RowIdx.conj_diag_val (ϖ : kˣ) (t : ι) (z : GL ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s =
      (if r = t then (ϖ : k)⁻¹ else 1) * z.val r s * (if s = t then (ϖ : k) else 1) := by sorry
