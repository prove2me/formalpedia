-- Prove2me | Theorems.Thm_GlobalTheory_latticeMean_const_mul
-- name    : GlobalTheory.latticeMean_const_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:53.079307+00:00
-- url     : https://prove2.me/theorems/d55a9568-9953-4e92-809a-38996b858983
-- title:
--   Global Theory: lattice Mean const mul
-- statement:
--   The Global Theory construction uses the lattice Mean const mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L118-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Submodule Set
open GlobalTheory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem GlobalTheory.latticeMean_const_mul {𝕜 : Type*} [RCLike 𝕜] (c : 𝕜) (f : E → 𝕜) :
    latticeMean L (fun x => c * f x) = c * latticeMean L f := by sorry
