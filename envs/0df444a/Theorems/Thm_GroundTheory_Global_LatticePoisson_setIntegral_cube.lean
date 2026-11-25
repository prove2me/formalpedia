-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_setIntegral_cube
-- name    : GroundTheory.Global.LatticePoisson.setIntegral_cube
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:41.503433+00:00
-- url     : https://prove2.me/theorems/d297604b-c8a7-4ef3-b76d-c897c6be400a
-- title:
--   Lattice Poisson: set Integral cube
-- statement:
--   The Lattice Poisson construction uses the set Integral cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L191-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L191-L232

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
omit [DecidableEq ι]

theorem GroundTheory.Global.LatticePoisson.setIntegral_cube (φ : E → ℂ) :
    ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ico (0 : ℝ) 1}, φ ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
      (ZLattice.covolume L)⁻¹ • ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L), φ y := by sorry
