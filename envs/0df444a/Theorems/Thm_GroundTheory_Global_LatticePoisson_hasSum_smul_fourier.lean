-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_hasSum_smul_fourier
-- name    : GroundTheory.Global.LatticePoisson.hasSum_smul_fourier
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:20.933888+00:00
-- url     : https://prove2.me/theorems/14a5edde-9fd3-44a6-b6da-58a8fd74c94c
-- title:
--   Lattice Poisson: has Sum smul fourier
-- statement:
--   The Lattice Poisson construction uses the has Sum smul fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L273-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L273-L287

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

theorem GroundTheory.Global.LatticePoisson.hasSum_smul_fourier (f : 𝓢(E, ℂ)) (a : E) :
    HasSum (fun μ : dualLattice L => (ZLattice.covolume L)⁻¹ • (𝓕 (f : E → ℂ) μ * 𝐞 ⟪(μ : E), a⟫))
      (per L f a) := by sorry
