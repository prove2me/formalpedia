-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_perTorus_toTorus
-- name    : GroundTheory.Global.LatticePoisson.perTorus_toTorus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:21.542834+00:00
-- url     : https://prove2.me/theorems/e4ed23ee-c9ea-4071-9704-6b6b1cae96b9
-- title:
--   Lattice Poisson: per Torus to Torus
-- statement:
--   The Lattice Poisson construction uses the per Torus to Torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L140-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L140-L143

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
omit [DecidableEq ι]

theorem GroundTheory.Global.LatticePoisson.perTorus_toTorus (f : 𝓢(E, ℂ)) (x : ι → ℝ) :
    perTorus b f (toTorus x) = per L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x) := by sorry
