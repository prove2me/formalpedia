-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_conj_int_iff
-- name    : GlobalTheory.DiagVol.RowIdx.conj_int_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:50:00.653779+00:00
-- url     : https://prove2.me/theorems/621c381f-c2f4-40e0-a96e-fe20dabbedb4
-- title:
--   Row Idx: conj int iff
-- statement:
--   The Row Idx construction uses the conj int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L74-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L74-L92

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

theorem GlobalTheory.DiagVol.RowIdx.conj_int_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : GL ι k) (hz : ∀ r s, z.val r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s ∈ 𝒪[k]) ↔
      ∀ s, s ≠ t → (ϖ : k)⁻¹ * z.val t s ∈ 𝒪[k] := by sorry
