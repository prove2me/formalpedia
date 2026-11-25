-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_latticeMean_eq_zero
-- name    : GlobalTheory.eq_zero_of_latticeMean_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:02.213046+00:00
-- url     : https://prove2.me/theorems/08c80d6f-a6a0-4035-bf85-f856fd6f1742
-- title:
--   Global Theory: eq zero of lattice Mean eq zero
-- statement:
--   The Global Theory construction uses the eq zero of lattice Mean eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L145-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L145-L167

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

theorem GlobalTheory.eq_zero_of_latticeMean_eq_zero {f : E → ℝ} (hc : Continuous f) (h0 : ∀ x, 0 ≤ f x)
    (hf : ∀ a ∈ L, ∀ x, f (x + a) = f x) (h : latticeMean L f = 0) : f = 0 := by sorry
