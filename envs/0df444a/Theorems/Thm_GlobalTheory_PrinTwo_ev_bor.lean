-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_ev_bor
-- name    : GlobalTheory.PrinTwo.ev_bor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:13.7138+00:00
-- url     : https://prove2.me/theorems/45bac2a2-c1a3-4547-b95d-ea99f746a3a1
-- title:
--   Prin Two: ev bor
-- statement:
--   The Prin Two construction uses the ev bor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L114-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L114-L155

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

theorem GlobalTheory.PrinTwo.ev_bor {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (a d : kˣ) (x : k) (g : GL (Fin (1 + 1)) k) :
    ev f (bor a d x * g) = bchar μ₁ μ₂ a d * ev f g := by sorry
