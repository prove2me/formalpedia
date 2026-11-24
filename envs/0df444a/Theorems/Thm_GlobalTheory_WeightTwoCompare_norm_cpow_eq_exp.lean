-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoCompare_norm_cpow_eq_exp
-- name    : GlobalTheory.WeightTwoCompare.norm_cpow_eq_exp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:25.905255+00:00
-- url     : https://prove2.me/theorems/51806911-b1b3-4cc9-b906-2fc0ddd3068d
-- title:
--   Weight Two Compare: norm cpow eq exp
-- statement:
--   The Weight Two Compare construction uses the norm cpow eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L18-L25

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumDeformedLatticeEisensteinSummandWeightTwo
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
open GlobalTheory GlobalTheory.WeightTwoCompare
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.WeightTwoCompare.norm_cpow_eq_exp {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by sorry
