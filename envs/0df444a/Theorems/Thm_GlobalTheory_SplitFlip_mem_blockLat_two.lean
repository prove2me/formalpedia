-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_blockLat_two
-- name    : GlobalTheory.SplitFlip.mem_blockLat_two
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:24:29.248938+00:00
-- url     : https://prove2.me/theorems/66f3f872-c269-52cd-bf7b-9f7db689f008
-- title:
--   Split Flip: mem block Lat two
-- statement:
--   The Split Flip construction uses the mem block Lat two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L853-L856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L853-L856

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]

theorem GlobalTheory.SplitFlip.mem_blockLat_two (ϖ : kˣ) (e : ℕ) (x : D₁ ⊕ D₂ → k) :
    x ∈ blockLat ϖ e (Assignment.two.block D₁ D₂) ↔ (∀ j, valuation k (x (.inl j)) ≤ 1) ∧
      ∀ j, valuation k (x (.inr j)) ≤ valuation k (((ϖ ^ e)⁻¹ : kˣ) : k) := by sorry
