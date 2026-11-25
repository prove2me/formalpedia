-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Model_exists_flip_ne_zero
-- name    : GlobalTheory.SplitFlip.Model.exists_flip_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:25:38.055099+00:00
-- url     : https://prove2.me/theorems/fc685c58-50dd-48c3-8cfb-84a936fb0611
-- title:
--   Model: exists flip ne zero
-- statement:
--   The Model construction uses the exists flip ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L194-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/OmAUnipFourierInv.lean#L194-L222

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
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitFlip.Model.exists_flip_ne_zero (t s : ℕ) (ht : Odd t) (hs : Odd s) (a : Assignment) :
    ∃ (G : Grid k) (ϖ : kˣ) (ψ : AddChar k Circle) (S : G.PiLocalization₂), G.m = 1 ∧ G.t = t ∧ G.s = s ∧ G.IsGood ϖ ψ 2 ∧
      S.path = givenPath 1 ∧ S.IsAdmissible a ϖ 2 ∧ PassesThrough 0 0 S.path ∧
      (S.flip a ψ ϖ 2 (0, 0)).path = oppositePath 1 ∧ (S.flip a ψ ϖ 2 (0, 0)).tensor ≠ 0 := by sorry
