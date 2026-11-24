-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_bchar_ne_zero
-- name    : GlobalTheory.PrinTwo.bchar_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:55:26.910596+00:00
-- url     : https://prove2.me/theorems/75f97a02-6df4-4840-a63a-d6e11fc05146
-- title:
--   Prin Two: bchar ne zero
-- statement:
--   The Prin Two construction uses the bchar ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L181-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L181-L181

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

theorem GlobalTheory.PrinTwo.bchar_ne_zero (μ₁ μ₂ : kˣ →* ℂˣ) (a d : kˣ) : bchar μ₁ μ₂ a d ≠ 0 := by sorry
