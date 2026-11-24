-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_isPrimitiveFrame_standardBasis
-- name    : GlobalTheory.SplitFlip.isPrimitiveFrame_standardBasis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:59.062291+00:00
-- url     : https://prove2.me/theorems/73f8eaf6-6dc1-4cd9-bffd-ee687a90dab1
-- title:
--   Split Flip: is Primitive Frame standard Basis
-- statement:
--   The Split Flip construction uses the is Primitive Frame standard Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L420-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L420-L432

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
variable {A D : Type*}
variable [Fintype D]

theorem GlobalTheory.SplitFlip.isPrimitiveFrame_standardBasis [Fintype A] [DecidableEq D] {A' : Type*} [Fintype A'] (σ : A ⊕ A' ≃ D) :
    IsPrimFrame (stdLat k D) (X0 k σ) := by sorry
