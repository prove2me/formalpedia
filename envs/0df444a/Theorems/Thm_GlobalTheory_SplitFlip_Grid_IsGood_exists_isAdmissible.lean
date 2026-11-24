-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_Grid_IsGood_exists_isAdmissible
-- name    : GlobalTheory.SplitFlip.Grid.IsGood.exists_isAdmissible
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:19:44.065926+00:00
-- url     : https://prove2.me/theorems/313ff64d-c022-4a88-b3b6-ca9089b036d5
-- title:
--   Is Good: exists is Admissible
-- statement:
--   The Is Good construction uses the exists is Admissible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1130-L1157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L1130-L1157

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

theorem GlobalTheory.SplitFlip.Grid.IsGood.exists_isAdmissible {G : Grid k} {ϖ : kˣ} {ψ : AddChar k Circle} {e : ℕ} (h : G.IsGood ϖ ψ e)
    (hϖ : IsUnif ϖ) (s : Assignment) {γ : List Edge} (hγ : IsPath γ) (hm : ∀ b ∈ γ, b.InGrid G.m) :
    ∃ S : G.PiLocalization₂, S.path = γ ∧ S.IsAdmissible s ϖ e ∧ S.tensor 0 = 1 := by sorry
