-- Prove2me | Theorems.Thm_GlobalTheory_PeriodicWeierstrass_tendsto_leading
-- name    : GlobalTheory.PeriodicWeierstrass.tendsto_leading
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:44:30.438521+00:00
-- url     : https://prove2.me/theorems/1bda06dc-313b-4d1a-901c-8dadbc390275
-- title:
--   Periodic Weierstrass: tendsto leading
-- statement:
--   The Periodic Weierstrass construction uses the tendsto leading property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L332-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/ExistsConstOfSqMulTendstoZero.lean#L332-L386

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

theorem GlobalTheory.PeriodicWeierstrass.tendsto_leading (W : WeierstrassCurve ℂ)
    {x y t : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hE : ∀ᶠ z in 𝓝[≠] 0, W.toAffine.Equation (x z) (y z))
    (ht : AnalyticAt ℂ t 0) (ht0 : t 0 = 0) (ht1 : deriv t 0 = c)
    (hty : ∀ᶠ z in 𝓝[≠] 0, t z * y z = -x z)
    (hy : Tendsto (fun z ↦ ‖y z‖) (𝓝[≠] 0) atTop) :
    Tendsto (fun z ↦ z ^ 2 * (c ^ 2 * x z)) (𝓝[≠] 0) (𝓝 1) ∧
      Tendsto (fun z ↦ z ^ 3 * (c ^ 3 * y z)) (𝓝[≠] 0) (𝓝 (-1)) := by sorry
