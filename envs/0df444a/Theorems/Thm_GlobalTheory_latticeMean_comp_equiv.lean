-- Prove2me | Theorems.Thm_GlobalTheory_latticeMean_comp_equiv
-- name    : GlobalTheory.latticeMean_comp_equiv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:01:31.669838+00:00
-- url     : https://prove2.me/theorems/3fbd3a7b-1570-4230-ab5a-e3ea278897e0
-- title:
--   Global Theory: lattice Mean comp equiv
-- statement:
--   The Global Theory construction uses the lattice Mean comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L195-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L195-L221

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

theorem GlobalTheory.latticeMean_comp_equiv {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] (L' : Submodule ℤ E') [DiscreteTopology L'] [IsZLattice ℝ L']
    (e : E ≃L[ℝ] E') (he : ∀ x, e x ∈ L' ↔ x ∈ L) {f : E' → G}
    (hf : ∀ a ∈ L', ∀ x, f (x + a) = f x) :
    latticeMean L (fun x => f (e x)) = latticeMean L' f := by sorry
