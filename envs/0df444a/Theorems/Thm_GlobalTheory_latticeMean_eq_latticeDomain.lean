-- Prove2me | Theorems.Thm_GlobalTheory_latticeMean_eq_latticeDomain
-- name    : GlobalTheory.latticeMean_eq_latticeDomain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:27.439982+00:00
-- url     : https://prove2.me/theorems/d14da167-0430-4760-b1c0-67f34399046c
-- title:
--   Global Theory: lattice Mean eq lattice Domain
-- statement:
--   The Global Theory construction uses the lattice Mean eq lattice Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L89-L93

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

theorem GlobalTheory.latticeMean_eq_latticeDomain [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (f : E → G) :
    latticeMean L f = (ZLattice.covolume L μ)⁻¹ • ∫ x in latticeDomain L, f x ∂μ := by sorry
