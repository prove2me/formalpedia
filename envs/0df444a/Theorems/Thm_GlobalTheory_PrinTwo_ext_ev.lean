-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_ext_ev
-- name    : GlobalTheory.PrinTwo.ext_ev
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:55:17.875105+00:00
-- url     : https://prove2.me/theorems/e1f4a468-5828-4bf8-b766-36d0404131f1
-- title:
--   Prin Two: ext ev
-- statement:
--   The Prin Two construction uses the ext ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L94-L96

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

theorem GlobalTheory.PrinTwo.ext_ev {μ₁ μ₂ : kˣ →* ℂˣ} {f f' : PSp μ₁ μ₂} (h : ∀ g, ev f g = ev f' g) : f = f' := by sorry
