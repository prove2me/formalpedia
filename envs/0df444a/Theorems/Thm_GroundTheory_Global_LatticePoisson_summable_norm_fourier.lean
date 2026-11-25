-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_summable_norm_fourier
-- name    : GroundTheory.Global.LatticePoisson.summable_norm_fourier
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:59.427805+00:00
-- url     : https://prove2.me/theorems/786ba5b3-7def-4d54-a021-47b63a3441f1
-- title:
--   Lattice Poisson: summable norm fourier
-- statement:
--   The Lattice Poisson construction uses the summable norm fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L259-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L259-L261

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
variable [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Global.LatticePoisson.summable_norm_fourier (f : 𝓢(E, ℂ)) :
    Summable fun μ : dualLattice L => ‖𝓕 (f : E → ℂ) μ‖ := by sorry
