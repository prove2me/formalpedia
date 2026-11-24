-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_ev_act
-- name    : GlobalTheory.PrinTwo.ev_act
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:48.8798+00:00
-- url     : https://prove2.me/theorems/086b30e4-5f9f-42eb-9285-90d3e07fbe3c
-- title:
--   Prin Two: ev act
-- statement:
--   The Prin Two construction uses the ev act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L91-L92

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

theorem GlobalTheory.PrinTwo.ev_act {μ₁ μ₂ : kˣ →* ℂˣ} (h : GL (Fin (1 + 1)) k) (f : PSp μ₁ μ₂) (g : GL (Fin (1 + 1)) k) :
    ev (psRep μ₁ μ₂ h f) g = ev f (g * h) := by sorry
