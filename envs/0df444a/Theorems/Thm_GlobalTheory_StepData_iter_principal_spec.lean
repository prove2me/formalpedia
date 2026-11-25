-- Prove2me | Theorems.Thm_GlobalTheory_StepData_iter_principal_spec
-- name    : GlobalTheory.StepData.iter_principal_spec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:49.01992+00:00
-- url     : https://prove2.me/theorems/faf86a76-ee0f-5a59-aea6-d41db6e74274
-- title:
--   Step Data: iter principal spec
-- statement:
--   The Step Data construction uses the iter principal spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IterPrincipalSpec.lean#L155-L156

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

theorem GlobalTheory.StepData.iter_principal_spec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, GlobalTheory.SplitWeil.IsTame (μ j)) (j : ℕ), (∀ g : GL (Ix r t j) k, g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ GlobalTheory.SplitWeil.KO k (Ix r t j) ∧ (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1)) ∧ ∀ (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ), (∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) → ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) := by sorry
