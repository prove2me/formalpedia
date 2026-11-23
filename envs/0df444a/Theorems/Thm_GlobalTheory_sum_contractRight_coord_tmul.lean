-- Prove2me | Theorems.Thm_GlobalTheory_sum_contractRight_coord_tmul
-- name    : GlobalTheory.sum_contractRight_coord_tmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:00.526373+00:00
-- url     : https://prove2.me/theorems/97d45afd-3b2c-47c4-845a-b8e1d0fbd486
-- title:
--   Global Theory: sum contract Right coord tmul
-- statement:
--   The Global Theory construction uses the sum contract Right coord tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DvdTraceOfBalancedTensor.lean#L66-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]

theorem GlobalTheory.sum_contractRight_coord_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) : ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] b j = Θ := by sorry
