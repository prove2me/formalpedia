-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_red_row_off
-- name    : GlobalTheory.DiagVol.RowIdx.red_row_off
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:19.676813+00:00
-- url     : https://prove2.me/theorems/7a1dfe13-2bd0-4309-b9c8-b5956df47871
-- title:
--   Row Idx: red row off
-- statement:
--   The Row Idx construction uses the red row off property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L98-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L98-L109

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

theorem GlobalTheory.DiagVol.RowIdx.red_row_off {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι} {S : Finset ι}
    (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) (s : ι) (hs : s ∉ S) :
    (red (Subgroup.inclusion hHK z)).val t s = (1 : Matrix ι ι 𝓀[k]) t s := by sorry
