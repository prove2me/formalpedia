-- Prove2me | Theorems.Thm_GlobalTheory_IndexCol_conj_apply
-- name    : GlobalTheory.IndexCol.conj_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:54.676884+00:00
-- url     : https://prove2.me/theorems/26f75442-474b-4c90-a6c1-e33a60cfd067
-- title:
--   Index Col: conj apply
-- statement:
--   The Index Col construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexConjIntegralGLColumnCongruence.lean#L36-L40

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

theorem GlobalTheory.IndexCol.conj_apply (ϖ : kˣ) (t : ι) (z : Matrix ι ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ : ι → kˣ)).val * z * ((diagGL (Pi.mulSingle t ϖ : ι → kˣ))⁻¹).val) r s =
      ((Pi.mulSingle t ϖ : ι → kˣ) r : k) * z r s * ((((Pi.mulSingle t ϖ : ι → kˣ) s)⁻¹ : kˣ) : k) := by sorry
