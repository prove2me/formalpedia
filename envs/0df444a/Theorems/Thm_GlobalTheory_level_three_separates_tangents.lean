-- Prove2me | Theorems.Thm_GlobalTheory_level_three_separates_tangents
-- name    : GlobalTheory.level_three_separates_tangents
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:07:16.57333+00:00
-- url     : https://prove2.me/theorems/26014bcc-57f8-40cd-90a3-a54c66e0817a
-- title:
--   Global Theory: level three separates tangents
-- statement:
--   The Global Theory construction uses the level three separates tangents property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L124-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LevelThreeSeparatesTangents.lean#L124-L212

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
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.level_three_separates_tangents {ι : Type} [Fintype ι] (Y : GT ι) (θ : EuclideanSpace ℂ ι → ℂ) (hθ : θ ∈ Y.Sec 1) (h0 : θ ≠ 0)
    (c₀ : ℂ) (c : EuclideanSpace ℂ ι)
    (h : ∀ a b, c₀ * (θ a * θ b * θ (-a - b)) + fderiv ℂ (fun v => θ (v + a) * θ (v + b) * θ (v - a - b)) 0 c = 0) : c = 0 ∧ c₀ = 0 := by sorry
