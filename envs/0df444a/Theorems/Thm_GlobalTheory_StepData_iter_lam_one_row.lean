-- Prove2me | Theorems.Thm_GlobalTheory_StepData_iter_lam_one_row
-- name    : GlobalTheory.StepData.iter_lam_one_row
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:11:25.532567+00:00
-- url     : https://prove2.me/theorems/9c9394d5-f629-4b44-b05a-a18ad5c454c2
-- title:
--   Step Data: iter lam one row
-- statement:
--   The Step Data construction uses the iter lam one row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedDepthOneLevelCharOfOneRowFirstBlock.lean#L20-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IteratedDepthOneLevelCharOfOneRowFirstBlock.lean#L20-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IteratedDepthOneLevelCharOfOneRowFirstBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
open GlobalTheory GlobalTheory.StepData

theorem GlobalTheory.StepData.iter_lam_one_row (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) : ∀ (h : (P.iter t μ hμ j).J),
    (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) →
    (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 →
    ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧
      (P.iter t μ hμ j).lam h = P.lam g := by sorry
