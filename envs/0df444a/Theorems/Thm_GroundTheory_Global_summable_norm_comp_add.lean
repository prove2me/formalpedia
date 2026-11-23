-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_norm_comp_add
-- name    : GroundTheory.Global.summable_norm_comp_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:53.818289+00:00
-- url     : https://prove2.me/theorems/d5c36218-6a94-409d-8e7b-09fda927d6a4
-- title:
--   Global: summable norm comp add
-- statement:
--   The Global construction uses the summable norm comp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L97-L100

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

theorem GroundTheory.Global.summable_norm_comp_add (Λ : Submodule ℤ E) [DiscreteTopology Λ]
    (g : 𝓢(E, F)) (x : E) : Summable fun ℓ : Λ => ‖g (x + ℓ)‖ := by sorry
