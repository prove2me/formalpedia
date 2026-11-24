-- Prove2me | Theorems.Thm_GlobalTheory_latticeMean_comp_add
-- name    : GlobalTheory.latticeMean_comp_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:36.421526+00:00
-- url     : https://prove2.me/theorems/cff0fa57-145a-471d-b99e-534960f85c54
-- title:
--   Global Theory: lattice Mean comp add
-- statement:
--   The Global Theory construction uses the lattice Mean comp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L129-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L129-L143

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

theorem GlobalTheory.latticeMean_comp_add {f : E → G} (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) (w : E) :
    latticeMean L (fun x => f (x + w)) = latticeMean L f := by sorry
