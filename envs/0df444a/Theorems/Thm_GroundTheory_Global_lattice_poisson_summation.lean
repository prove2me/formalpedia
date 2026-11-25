-- Prove2me | Theorems.Thm_GroundTheory_Global_lattice_poisson_summation
-- name    : GroundTheory.Global.lattice_poisson_summation
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:27:52.567405+00:00
-- url     : https://prove2.me/theorems/e9508208-85d0-431d-9515-416606ddb883
-- title:
--   Global: lattice poisson summation
-- statement:
--   The Global construction uses the lattice poisson summation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L306-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L306-L311

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

theorem GroundTheory.Global.lattice_poisson_summation (f : 𝓢(E, ℂ)) (a : E) :
    ∑' ℓ : L, f (ℓ + a) =
      (ZLattice.covolume L)⁻¹ • ∑' μ : dualLattice L, 𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫ := by sorry
