-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicWeierstrass_exists_eq_of_cube_mul_tendsto
-- name    : GlobalTheory.PeriodicWeierstrass.exists_eq_of_cube_mul_tendsto
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:44:37.040018+00:00
-- url     : https://prove2.me/theorems/8936babb-71b0-452d-b41c-6db728661f7d
-- title:
--   Periodic Weierstrass: exists eq of cube mul tendsto
-- statement:
--   The Periodic Weierstrass construction uses the exists eq of cube mul tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L306-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L306-L327

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
open GlobalTheory.PeriodicWeierstrass
variable (L : PeriodPair)
open Filter PeriodPair
open scoped Topology

theorem GlobalTheory.PeriodicWeierstrass.exists_eq_of_cube_mul_tendsto (L : PeriodPair) {g : ℂ → ℂ}
    (hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z) (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z)
    (h : Tendsto (fun z ↦ z ^ 3 * g z) (𝓝[≠] 0) (𝓝 (-2))) :
    ∃ b k, ∀ z ∉ L.lattice, g z = ℘'[L] z + b * ℘[L] z + k := by sorry
