-- Prove2me | Theorems.Thm_GlobalTheory_StepData_mem_iter_principal
-- name    : GlobalTheory.StepData.mem_iter_principal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:01:32.049304+00:00
-- url     : https://prove2.me/theorems/a8689c49-a5df-41a9-bb64-a365628cbae2
-- title:
--   Step Data: mem iter principal
-- statement:
--   The Step Data construction uses the mem iter principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L42-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L42-L113

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

theorem GlobalTheory.StepData.mem_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix r t j) k) :
    g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ KO k (Ix r t j) ∧
      (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1) := by sorry
