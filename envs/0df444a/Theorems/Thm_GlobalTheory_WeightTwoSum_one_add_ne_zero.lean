-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoSum_one_add_ne_zero
-- name    : GlobalTheory.WeightTwoSum.one_add_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:19.863963+00:00
-- url     : https://prove2.me/theorems/86f8e841-3342-4daa-a6b9-ef6fb67a43ba
-- title:
--   Weight Two Sum: one add ne zero
-- statement:
--   The Weight Two Sum construction uses the one add ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DifferentiableRisingS.lean#L60-L65

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
omit [Fintype I]

theorem GlobalTheory.WeightTwoSum.one_add_ne_zero {z : I → ℂ} (hz : z ∈ polydisc I) (i : I) : 1 + z i ≠ 0 := by sorry
