-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoSum_homFac_ne_zero
-- name    : GlobalTheory.WeightTwoSum.homFac_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:34.812813+00:00
-- url     : https://prove2.me/theorems/5923bd43-c2a9-4799-9035-7c071e2479d6
-- title:
--   Weight Two Sum: hom Fac ne zero
-- statement:
--   The Weight Two Sum construction uses the hom Fac ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L67-L70

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

theorem GlobalTheory.WeightTwoSum.homFac_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) : homFac z ≠ 0 := by sorry
