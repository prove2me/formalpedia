-- Prove2me | Theorems.Thm_GlobalTheory_covolume_span_basis_eq_sqrt_det_gram
-- name    : GlobalTheory.covolume_span_basis_eq_sqrt_det_gram
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:14:49.788795+00:00
-- url     : https://prove2.me/theorems/560d8c84-3aba-4d2c-a458-79c3e94ab81d
-- title:
--   Global Theory: covolume span basis eq sqrt det gram
-- statement:
--   The Global Theory construction uses the covolume span basis eq sqrt det gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LinearIndependentRealOfIntOfDiscrete.lean#L91-L100

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
variable [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.covolume_span_basis_eq_sqrt_det_gram [DecidableEq ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = √(gram ℝ b).det := by sorry
