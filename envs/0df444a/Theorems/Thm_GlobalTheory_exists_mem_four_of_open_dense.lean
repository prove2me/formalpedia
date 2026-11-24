-- Prove2me | Theorems.Thm_GlobalTheory_exists_mem_four_of_open_dense
-- name    : GlobalTheory.exists_mem_four_of_open_dense
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:40.509521+00:00
-- url     : https://prove2.me/theorems/87fc3060-2f52-4234-bc4c-bc42a7088765
-- title:
--   Global Theory: exists mem four of open dense
-- statement:
--   The Global Theory construction uses the exists mem four of open dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L15-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
omit [NormedSpace ℂ V]

theorem GlobalTheory.exists_mem_four_of_open_dense {U : Set V} (ho : IsOpen U) (hd : Dense U)
    (e₁ e₂ e₃ e₄ : V ≃ₜ V) : ∃ x, e₁ x ∈ U ∧ e₂ x ∈ U ∧ e₃ x ∈ U ∧ e₄ x ∈ U := by sorry
