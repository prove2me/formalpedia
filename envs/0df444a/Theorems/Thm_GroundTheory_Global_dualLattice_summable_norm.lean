-- Prove2me | Theorems.Thm_GroundTheory_Global_dualLattice_summable_norm
-- name    : GroundTheory.Global.dualLattice_summable_norm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:25.84411+00:00
-- url     : https://prove2.me/theorems/74e6016b-be60-4b55-835f-0b9c27bcc7ce
-- title:
--   Global: dual Lattice summable norm
-- statement:
--   The Global construction uses the dual Lattice summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L302-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L302-L304

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

theorem GroundTheory.Global.dualLattice_summable_norm (f : 𝓢(E, ℂ)) (a : E) :
    Summable fun μ : dualLattice L => ‖𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫‖ := by sorry
