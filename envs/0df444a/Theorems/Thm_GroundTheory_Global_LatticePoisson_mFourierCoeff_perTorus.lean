-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_mFourierCoeff_perTorus
-- name    : GroundTheory.Global.LatticePoisson.mFourierCoeff_perTorus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:29.055066+00:00
-- url     : https://prove2.me/theorems/69234af6-1e5a-4371-a0f6-6b15008bc6e7
-- title:
--   Lattice Poisson: m Fourier Coeff per Torus
-- statement:
--   The Lattice Poisson construction uses the m Fourier Coeff per Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L234-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L234-L257

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

theorem GroundTheory.Global.LatticePoisson.mFourierCoeff_perTorus (f : 𝓢(E, ℂ)) (m : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (perTorus b f) m =
      (ZLattice.covolume L)⁻¹ • 𝓕 (f : E → ℂ) (dualPt b m) := by sorry
