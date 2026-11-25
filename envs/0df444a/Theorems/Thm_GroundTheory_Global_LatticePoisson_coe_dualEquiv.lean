-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_coe_dualEquiv
-- name    : GroundTheory.Global.LatticePoisson.coe_dualEquiv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:32.390855+00:00
-- url     : https://prove2.me/theorems/df0166f9-33a9-4a32-aab9-1472b5540032
-- title:
--   Lattice Poisson: coe dual Equiv
-- statement:
--   The Lattice Poisson construction uses the coe dual Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L79-L79

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson
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
open GroundTheory.Global.LatticePoisson
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)

theorem GroundTheory.Global.LatticePoisson.coe_dualEquiv (m : ι → ℤ) : (dualEquiv b m : E) = dualPt b m := by sorry
