-- Prove2me | Theorems.Thm_GroundTheory_Global_hasSum_lattice_poisson
-- name    : GroundTheory.Global.hasSum_lattice_poisson
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:56:30.596171+00:00
-- url     : https://prove2.me/theorems/c867be18-3c63-568b-8675-845e733e0b5e
-- title:
--   Global: has Sum lattice poisson
-- statement:
--   The Global construction uses the has Sum lattice poisson property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L313-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L313-L318

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

theorem GroundTheory.Global.hasSum_lattice_poisson (f : 𝓢(E, ℂ)) (a : E) :
    HasSum (fun μ : dualLattice L => 𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫)
      (ZLattice.covolume L • ∑' ℓ : L, f (ℓ + a)) := by sorry
