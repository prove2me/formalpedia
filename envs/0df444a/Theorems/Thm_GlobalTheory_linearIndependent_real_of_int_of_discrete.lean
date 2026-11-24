-- Prove2me | Theorems.Thm_GlobalTheory_linearIndependent_real_of_int_of_discrete
-- name    : GlobalTheory.linearIndependent_real_of_int_of_discrete
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:07:00.224961+00:00
-- url     : https://prove2.me/theorems/3580dd8b-287b-4556-8002-e4f2cfe6f6eb
-- title:
--   Global Theory: linear Independent real of int of discrete
-- statement:
--   The Global Theory construction uses the linear Independent real of int of discrete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L79-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem GlobalTheory.linearIndependent_real_of_int_of_discrete {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L]
    {v : ι → F} (hv : ∀ i, v i ∈ L) (hli : LinearIndependent ℤ v) : LinearIndependent ℝ v := by sorry
