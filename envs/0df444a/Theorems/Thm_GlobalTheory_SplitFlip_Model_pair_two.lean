-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_pair_two
-- name    : GlobalTheory.SplitFlip.Model.pair_two
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:19:49.623268+00:00
-- url     : https://prove2.me/theorems/ee770c60-3798-4690-a936-7b000c49e25c
-- title:
--   Model: pair two
-- statement:
--   The Model construction uses the pair two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L240-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L240-L250

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

theorem GlobalTheory.SplitFlip.Model.pair_two (Y : Matrix A (D₁ ⊕ D₂) k) (T : Matrix A (Assignment.two.block D₁ D₂) k) :
    pairCols _ Y T = ∑ i, ∑ j : D₂, setCols _ (0 : Matrix A (D₁ ⊕ D₂) k) T i (.inr j) * Y i (.inr j) := by sorry
