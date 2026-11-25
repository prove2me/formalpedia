-- Prove2me | Theorems.Thm_GroundTheory_Global_lattice_summable_norm
-- name    : GroundTheory.Global.lattice_summable_norm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:44.489126+00:00
-- url     : https://prove2.me/theorems/97676e3d-89b8-438b-ac71-0db7e91ce671
-- title:
--   Global: lattice summable norm
-- statement:
--   The Global construction uses the lattice summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L299-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L299-L300

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
omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L]

theorem GroundTheory.Global.lattice_summable_norm (f : 𝓢(E, ℂ)) (a : E) : Summable fun ℓ : L => ‖f (ℓ + a)‖ := by sorry
