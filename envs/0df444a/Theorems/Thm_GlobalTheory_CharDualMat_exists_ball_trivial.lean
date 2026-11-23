-- Prove2me | Theorems.Thm_GlobalTheory_CharDualMat_exists_ball_trivial
-- name    : GlobalTheory.CharDualMat.exists_ball_trivial
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:51.517811+00:00
-- url     : https://prove2.me/theorems/9bd4a8f4-4e5d-4f07-a578-2d162572fb89
-- title:
--   Char Dual Mat: exists ball trivial
-- statement:
--   The Char Dual Mat construction uses the exists ball trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixIntegralOfAddCharTraceDual.lean#L87-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixIntegralOfAddCharTraceDual.lean#L87-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegralOfAddCharTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.CharDualMat
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.CharDualMat.exists_ball_trivial (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : ValueGroupWithZero k, γ ≠ 0 ∧ ∀ t : k, valuation k t < γ → ψ t = 1 := by sorry
