-- Prove2me | Theorems.Thm_GlobalTheory_invariants_eq_of_periodic_solution
-- name    : GlobalTheory.invariants_eq_of_periodic_solution
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:42:06.951829+00:00
-- url     : https://prove2.me/theorems/52e06756-94e9-4c15-99fe-aa7f88d8e4cd
-- title:
--   Global Theory: invariants eq of periodic solution
-- statement:
--   The Global Theory construction uses the invariants eq of periodic solution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L393-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L393-L499

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsConstOfSqMulTendstoZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair
open scoped Topology
noncomputable section
open GlobalTheory
open Filter PeriodPair
open scoped Topology

theorem GlobalTheory.invariants_eq_of_periodic_solution :
    ∀ (L : PeriodPair) (W : WeierstrassCurve ℂ) (x y t : ℂ → ℂ) (c : ℂ), c ≠ 0 →
  DifferentiableOn ℂ x (L.lattice : Set ℂ)ᶜ → DifferentiableOn ℂ y (L.lattice : Set ℂ)ᶜ →
  (∀ l ∈ L.lattice, ∀ z, x (z + l) = x z ∧ y (z + l) = y z) →
  (∀ z, z ∉ L.lattice → W.toAffine.Equation (x z) (y z)) →
  AnalyticAt ℂ t 0 → t 0 = 0 → deriv t 0 = c →
  (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) →
  Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop →
  c ^ 4 * W.c₄ = 12 * L.g₂ ∧ c ^ 6 * W.c₆ = 216 * L.g₃ ∧
    c ^ 12 * W.Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by sorry
