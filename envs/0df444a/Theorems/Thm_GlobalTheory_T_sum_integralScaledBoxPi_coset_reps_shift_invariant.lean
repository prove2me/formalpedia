-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_integralScaledBoxPi_coset_reps_shift_invariant
-- name    : GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:05:15.352647+00:00
-- url     : https://prove2.me/theorems/8e560e6e-2002-406a-8863-f5f631ff9870
-- title:
--   T: sum integral Scaled Box Pi coset reps shift invariant
-- statement:
--   The T construction uses the sum integral Scaled Box Pi coset reps shift invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement.lean#L12-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SumIntegralScaledBoxPiCosetRepsShiftInvariant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatConvolutionLocalFieldPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SumIntegralScaledBoxPiCosetRepsShiftInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi
open scoped Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_integralScaledBoxPi_coset_reps_shift_invariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] (r R : kˣ) (S : Finset (n → k)), (∀ b ∈ S, b ∈ box n R) → (∀ a ∈ box n R, ∃! b, b ∈ S ∧ a - b ∈ box n r) → ∀ F : (n → k) → ℂ, (∀ t ∈ box n r, ∀ y, F (y + t) = F y) → ∀ a ∈ box n R, ∑ b ∈ S, F (a + b) = ∑ b ∈ S, F b := by sorry
