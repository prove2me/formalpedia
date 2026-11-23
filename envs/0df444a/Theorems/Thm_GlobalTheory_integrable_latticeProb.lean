-- Prove2me | Theorems.Thm_GlobalTheory_integrable_latticeProb
-- name    : GlobalTheory.integrable_latticeProb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:34.560229+00:00
-- url     : https://prove2.me/theorems/791e5d25-b32b-4424-a2b3-502b6e0bfacc
-- title:
--   Global Theory: integrable lattice Prob
-- statement:
--   The Global Theory construction uses the integrable lattice Prob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsAddFundamentalDomainLatticeDomain.lean#L69-L75

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

theorem GlobalTheory.integrable_latticeProb {f : E → G} (hf : Continuous f) : Integrable f (latticeProb L) := by sorry
