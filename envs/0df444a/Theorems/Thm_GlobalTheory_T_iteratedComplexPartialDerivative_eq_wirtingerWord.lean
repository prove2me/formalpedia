-- Prove2me | Theorems.Thm_GlobalTheory_T_iteratedComplexPartialDerivative_eq_wirtingerWord
-- name    : GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:51:12.363382+00:00
-- url     : https://prove2.me/theorems/8ab31a98-6477-496d-8e24-d08c8bfc50f6
-- title:
--   T: iterated Complex Partial Derivative eq wirtinger Word
-- statement:
--   The T construction uses the iterated Complex Partial Derivative eq wirtinger Word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWordStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IteratedComplexPartialDerivativeEqWirtingerWordStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWord
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedComplexPartialDerivativeEqWirtingerWordStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord : ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Set (I → ℂ)) (g : (I → ℂ) → ℂ), IsOpen U → DifferentiableOn ℂ g U → ∀ (l : List I), ∀ z ∈ U, iterD l g z = wirtWord (l.map fun i => (i, false)) g z := by sorry
