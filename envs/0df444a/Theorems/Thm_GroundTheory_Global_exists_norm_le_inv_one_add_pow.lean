-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_norm_le_inv_one_add_pow
-- name    : GroundTheory.Global.exists_norm_le_inv_one_add_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:29.343931+00:00
-- url     : https://prove2.me/theorems/c8354bc4-afe8-4f03-b019-8be13b2efcb4
-- title:
--   Global: exists norm le inv one add pow
-- statement:
--   The Global construction uses the exists norm le inv one add pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L55-L64

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [FiniteDimensional ℝ E]

theorem GroundTheory.Global.exists_norm_le_inv_one_add_pow (g : 𝓢(E, F)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ x, ‖g x‖ ≤ C * ((1 + ‖x‖) ^ k)⁻¹ := by sorry
