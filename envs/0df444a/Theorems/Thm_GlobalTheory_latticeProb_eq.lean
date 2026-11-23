-- Prove2me | Theorems.Thm_GlobalTheory_latticeProb_eq
-- name    : GlobalTheory.latticeProb_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:44.140645+00:00
-- url     : https://prove2.me/theorems/1ab6f027-05df-4884-900d-35c59762470e
-- title:
--   Global Theory: lattice Prob eq
-- statement:
--   The Global Theory construction uses the lattice Prob eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L51-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L51-L60

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
variable [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.latticeProb_eq (μ : Measure E) [μ.IsAddHaarMeasure] :
    latticeProb L = (ENNReal.ofReal (ZLattice.covolume L μ))⁻¹ • μ.restrict (latticeDomain L) := by sorry
