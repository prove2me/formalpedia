-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_inner_equivFun_symm_dualPt
-- name    : GroundTheory.Global.LatticePoisson.inner_equivFun_symm_dualPt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:07.023981+00:00
-- url     : https://prove2.me/theorems/fb442145-dfc5-4507-b153-45635489ec98
-- title:
--   Lattice Poisson: inner equiv Fun symm dual Pt
-- statement:
--   The Lattice Poisson construction uses the inner equiv Fun symm dual Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L41-L45

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

theorem GroundTheory.Global.LatticePoisson.inner_equivFun_symm_dualPt (x : ι → ℝ) (m : ι → ℤ) :
    ⟪(b.ofZLatticeBasis ℝ L).equivFun.symm x, dualPt b m⟫ = ∑ i, (m i : ℝ) * x i := by sorry
