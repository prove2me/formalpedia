-- Prove2me | Theorems.Thm_GroundTheory_Global_continuous_tsum_comp_add
-- name    : GroundTheory.Global.continuous_tsum_comp_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:36.932272+00:00
-- url     : https://prove2.me/theorems/d2e2339f-160d-4b70-abb4-dd6e699f7586
-- title:
--   Global: continuous tsum comp add
-- statement:
--   The Global construction uses the continuous tsum comp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoissonBasic.lean#L102-L109

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

theorem GroundTheory.Global.continuous_tsum_comp_add [CompleteSpace F] (Λ : Submodule ℤ E)
    [DiscreteTopology Λ] (g : 𝓢(E, F)) : Continuous fun x => ∑' ℓ : Λ, g (x + ℓ) := by sorry
