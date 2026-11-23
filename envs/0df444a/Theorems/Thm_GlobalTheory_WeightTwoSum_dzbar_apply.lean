-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoSum_dzbar_apply
-- name    : GlobalTheory.WeightTwoSum.dzbar_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:01.873603+00:00
-- url     : https://prove2.me/theorems/f8242321-ceb3-4569-bc29-7eee7e2e821e
-- title:
--   Weight Two Sum: dzbar apply
-- statement:
--   The Weight Two Sum construction uses the dzbar apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L33-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped ContDiff
open GlobalTheory GlobalTheory.WeightTwoSum
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem GlobalTheory.WeightTwoSum.dzbar_apply (j : I) (v : I → ℂ) : dzbar j v = starRingEnd ℂ (v j) := by sorry

attribute [defeq] GlobalTheory.WeightTwoSum.dzbar_apply
