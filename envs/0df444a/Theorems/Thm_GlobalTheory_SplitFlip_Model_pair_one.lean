-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_pair_one
-- name    : GlobalTheory.SplitFlip.Model.pair_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:49.507082+00:00
-- url     : https://prove2.me/theorems/6d4251ee-a816-4d6e-94c6-bd8057889a9f
-- title:
--   Model: pair one
-- statement:
--   The Model construction uses the pair one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L254-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L254-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_OmAUnipFourierInv
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
open GlobalTheory GlobalTheory.SplitFlip GlobalTheory.SplitFlip.Model
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D₁ D₂ : Type*} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq A]

theorem GlobalTheory.SplitFlip.Model.pair_one (Y : Matrix A (D₁ ⊕ D₂) k) (T : Matrix A (Assignment.one.block D₁ D₂) k) :
    pairCols _ Y T = ∑ i, ∑ j : D₁, setCols _ (0 : Matrix A (D₁ ⊕ D₂) k) T i (.inl j) * Y i (.inl j) := by sorry
