-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_omB_shearGL
-- name    : GlobalTheory.RankChart.omB_shearGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:43:43.639241+00:00
-- url     : https://prove2.me/theorems/44a44fc0-f655-454d-82f6-4233f403e66e
-- title:
--   Rank Chart: om B shear GL
-- statement:
--   The Rank Chart construction uses the om B shear GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShearGLTransposeMul.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubMemNsp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Matrix
noncomputable section
open GlobalTheory GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RankChart.omB_shearGL (ν : kˣ →* ℂˣ) (c : Matrix T R k) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (shearGL c) 1 Ψ Y = Ψ (shear c Y) := by sorry
