-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_evL_apply
-- name    : GlobalTheory.PrinTwo.evL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:21.783802+00:00
-- url     : https://prove2.me/theorems/a807ca33-e4d6-4caa-bdc7-66c3148d93e8
-- title:
--   Prin Two: ev L apply
-- statement:
--   The Prin Two construction uses the ev L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L167-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L167-L168

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.PrinTwo.evL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (g : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) :
    evL μ₁ μ₂ g f = ev f g := by sorry

attribute [defeq] GlobalTheory.PrinTwo.evL_apply
