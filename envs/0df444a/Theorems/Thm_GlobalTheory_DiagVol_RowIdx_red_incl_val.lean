-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_incl_val
-- name    : GlobalTheory.DiagVol.RowIdx.red_incl_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:28.14382+00:00
-- url     : https://prove2.me/theorems/55d97ff5-789b-4934-810d-ecd3d4df873d
-- title:
--   Row Idx: red incl val
-- statement:
--   The Row Idx construction uses the red incl val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L94-L96

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

theorem GlobalTheory.DiagVol.RowIdx.red_incl_val {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) (z : H) (r s : ι) (h : (z : GL ι k).val r s ∈ 𝒪[k]) :
    (red (Subgroup.inclusion hHK z)).val r s = IsLocalRing.residue 𝒪[k] ⟨(z : GL ι k).val r s, h⟩ := by sorry
