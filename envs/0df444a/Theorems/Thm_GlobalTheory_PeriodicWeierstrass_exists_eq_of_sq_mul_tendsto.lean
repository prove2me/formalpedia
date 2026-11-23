-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicWeierstrass_exists_eq_of_sq_mul_tendsto
-- name    : GlobalTheory.PeriodicWeierstrass.exists_eq_of_sq_mul_tendsto
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:51.452555+00:00
-- url     : https://prove2.me/theorems/09302199-887a-49bf-98e3-f86bc65bdd68
-- title:
--   Periodic Weierstrass: exists eq of sq mul tendsto
-- statement:
--   The Periodic Weierstrass construction uses the exists eq of sq mul tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L161-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L161-L281

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

theorem GlobalTheory.PeriodicWeierstrass.exists_eq_of_sq_mul_tendsto (L : PeriodPair) {g : ℂ → ℂ} {a : ℂ}
    (hd : ∀ z ∉ L.lattice, DifferentiableAt ℂ g z) (hp : ∀ z, ∀ l ∈ L.lattice, g (z + l) = g z)
    (h : Tendsto (fun z ↦ z ^ 2 * g z) (𝓝[≠] 0) (𝓝 a)) :
    ∃ k, ∀ z ∉ L.lattice, g z = a * ℘[L] z + k := by sorry
