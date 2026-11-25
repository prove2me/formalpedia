-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_ev_act_bor_one
-- name    : GlobalTheory.PrinTwo.ev_act_bor_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:31.852624+00:00
-- url     : https://prove2.me/theorems/ccd9ef8a-8bd2-4550-8ea8-5f1cb6cd2efb
-- title:
--   Prin Two: ev act bor one
-- statement:
--   The Prin Two construction uses the ev act bor one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L185-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L185-L187

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

theorem GlobalTheory.PrinTwo.ev_act_bor_one {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) :
    ev (psRep μ₁ μ₂ (bor a d x) f) 1 = bchar μ₁ μ₂ a d * ev f 1 := by sorry
