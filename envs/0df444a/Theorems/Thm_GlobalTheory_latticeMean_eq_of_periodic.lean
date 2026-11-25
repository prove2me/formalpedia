-- Prove2me | Theorems.Thm_GlobalTheory_latticeMean_eq_of_periodic
-- name    : GlobalTheory.latticeMean_eq_of_periodic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:45.291875+00:00
-- url     : https://prove2.me/theorems/ef09c655-7d58-522c-a863-75b4b76aefb9
-- title:
--   Global Theory: lattice Mean eq of periodic
-- statement:
--   The Global Theory construction uses the lattice Mean eq of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L179-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L179-L193

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

theorem GlobalTheory.latticeMean_eq_of_periodic (L' : Submodule ℤ E) [DiscreteTopology L'] [IsZLattice ℝ L']
    [CompleteSpace G] {f : E → G} (hc : Continuous f) (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x)
    (hf' : ∀ a ∈ L', ∀ x, f (x + a) = f x) : latticeMean L f = latticeMean L' f := by sorry
