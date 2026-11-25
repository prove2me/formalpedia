-- Prove2me | Theorems.Thm_GlobalTheory_periodLattice_isLattice_of_mem_siegelH
-- name    : GlobalTheory.periodLattice_isLattice_of_mem_siegelH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:55.880795+00:00
-- url     : https://prove2.me/theorems/1584a351-2f08-4bf9-a364-62c3c7e1145f
-- title:
--   Global Theory: period Lattice is Lattice of mem siegel H
-- statement:
--   The Global Theory construction uses the period Lattice is Lattice of mem siegel H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L160-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MulVecOfRealVecAddMemSpanPeriodLattice.lean#L160-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.periodLattice_isLattice_of_mem_siegelH :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ ∈ SiegelH (Fin g) →
      DiscreteTopology (periodLattice τ) ∧
      Submodule.span ℝ (periodLattice τ : Set (Fin g → ℂ)) = ⊤ ∧
      ∀ n n' : Fin g → ℤ, τ *ᵥ ofIntVec n + ofIntVec n' = 0 → n = 0 ∧ n' = 0 := by sorry
