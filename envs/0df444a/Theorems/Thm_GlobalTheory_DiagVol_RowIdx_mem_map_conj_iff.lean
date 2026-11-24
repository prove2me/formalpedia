-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_RowIdx_mem_map_conj_iff
-- name    : GlobalTheory.DiagVol.RowIdx.mem_map_conj_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:37.787563+00:00
-- url     : https://prove2.me/theorems/f539dfed-41c6-4a44-b684-b2783f065aac
-- title:
--   Row Idx: mem map conj iff
-- statement:
--   The Row Idx construction uses the mem map conj iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L60-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLRowCongruence.lean#L60-L64

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

theorem GlobalTheory.DiagVol.RowIdx.mem_map_conj_iff (g : GL ι k) (K : Subgroup (GL ι k)) (z : GL ι k) :
    z ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ K := by sorry
