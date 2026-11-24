-- Prove2me | Theorems.Thm_GlobalTheory_exists_periodPair_of_lattice_in_line
-- name    : GlobalTheory.exists_periodPair_of_lattice_in_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:32.511624+00:00
-- url     : https://prove2.me/theorems/a7f9c67e-d876-4009-81a7-92ab66052034
-- title:
--   Global Theory: exists period Pair of lattice in line
-- statement:
--   The Global Theory construction uses the exists period Pair of lattice in line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsPeriodPairOfLatticeInLine.lean#L8-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsPeriodPairOfLatticeInLine.lean#L8-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsPeriodPairOfLatticeInLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.exists_periodPair_of_lattice_in_line :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (w : Fin g → ℂ), g = 1 → w ≠ 0 → DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∃ L : PeriodPair, ∀ z : ℂ, z ∈ L.lattice ↔ z • w ∈ Λ := by sorry
