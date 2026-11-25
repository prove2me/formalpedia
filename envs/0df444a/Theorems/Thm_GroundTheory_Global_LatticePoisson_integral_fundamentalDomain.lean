-- Prove2me | Theorems.Thm_GroundTheory_Global_LatticePoisson_integral_fundamentalDomain
-- name    : GroundTheory.Global.LatticePoisson.integral_fundamentalDomain
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:27:55.302621+00:00
-- url     : https://prove2.me/theorems/4da28ed1-4f70-4c9f-9d95-2bc9c583737e
-- title:
--   Lattice Poisson: integral fundamental Domain
-- statement:
--   The Lattice Poisson construction uses the integral fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L149-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LatticePoisson.lean#L149-L187

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

theorem GroundTheory.Global.LatticePoisson.integral_fundamentalDomain (f : 𝓢(E, ℂ)) {μ : E} (hμ : μ ∈ dualLattice L) :
    ∫ y in ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L),
      (𝐞 (-⟪y, μ⟫) : ℂ) * ∑' ℓ : L, f (y + ℓ) = 𝓕 (f : E → ℂ) μ := by sorry
