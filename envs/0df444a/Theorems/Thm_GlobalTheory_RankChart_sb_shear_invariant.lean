-- Prove2me | Theorems.Thm_GlobalTheory_RankChart_sb_shear_invariant
-- name    : GlobalTheory.RankChart.sb_shear_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:45.190799+00:00
-- url     : https://prove2.me/theorems/6d6bb43a-d96b-47d8-ae43-2ff37e9e6dba
-- title:
--   Rank Chart: sb shear invariant
-- statement:
--   The Rank Chart construction uses the sb shear invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartShearInvariance.lean#L15-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankChartShearInvariance.lean#L15-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShearGLTransposeMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankChartShearInvariance
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
open Filter
open scoped Topology
open GlobalTheory GlobalTheory.RankChart

theorem GlobalTheory.RankChart.sb_shear_invariant :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D],
      ∀ f ∈ SB (Matrix (R ⊕ T) D k), ∃ b : kˣ, ∀ (Y : Matrix (R ⊕ T) D k),
        ∀ c ∈ GlobalTheory.LocMod.Inhab.box T R b, f (GlobalTheory.RankChart.shear c Y) = f Y := by sorry
