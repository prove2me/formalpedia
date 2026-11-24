-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_mem_shellSet
-- name    : GlobalTheory.SplitFlip.mem_shellSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:42.470802+00:00
-- url     : https://prove2.me/theorems/36057ca4-23e6-4489-8bb5-1aebf77a3125
-- title:
--   Split Flip: mem shell Set
-- statement:
--   The Split Flip construction uses the mem shell Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L687-L689
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L687-L689

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
variable {A A' D : Type*} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D]

theorem GlobalTheory.SplitFlip.mem_shellSet {ϖ : kˣ} {n : A → ℤ} {g : GL A k} :
    g ∈ shellSet ϖ n ↔ ∃ x ∈ KO k A, ∃ y ∈ KO k A, g = x * (diagGL fun i => ϖ ^ n i) * y := by sorry
