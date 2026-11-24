-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_smallF_of_isEmpty
-- name    : GlobalTheory.SplitFlip.smallF_of_isEmpty
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:06:08.36387+00:00
-- url     : https://prove2.me/theorems/27e854cc-06ce-4bd6-89dc-d0d8f7b3a3a3
-- title:
--   Split Flip: small F of is Empty
-- statement:
--   The Split Flip construction uses the small F of is Empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L815-L823
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/RankEqCardIffExistsFrameMatrixFirstColumnBlock.lean#L815-L823

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
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitFlip.smallF_of_isEmpty [IsEmpty A'] (ν : kˣ →* ℂˣ) (Ψ : Matrix A' D k → ℂ) (Y : Matrix A' D k) :
    smallF (haarVol (KO k A')) ν Ψ Y = Ψ 0 := by sorry
