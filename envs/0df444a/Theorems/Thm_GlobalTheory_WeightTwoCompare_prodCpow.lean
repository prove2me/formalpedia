-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoCompare_prodCpow
-- name    : GlobalTheory.WeightTwoCompare.prodCpow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:21.856802+00:00
-- url     : https://prove2.me/theorems/71275f69-ddd5-4bd8-beb2-ce2255afc64e
-- title:
--   Weight Two Compare: prod Cpow
-- statement:
--   The Weight Two Compare construction uses the prod Cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L9-L16

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

theorem GlobalTheory.WeightTwoCompare.prodCpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w = (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w := by sorry
