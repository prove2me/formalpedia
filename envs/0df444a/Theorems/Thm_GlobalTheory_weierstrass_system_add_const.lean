-- Prove2me | Theorems.Thm_GlobalTheory_weierstrass_system_add_const
-- name    : GlobalTheory.weierstrass_system_add_const
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:25.371315+00:00
-- url     : https://prove2.me/theorems/c444e50e-0376-4809-9533-132de6d09b13
-- title:
--   Global Theory: weierstrass system add const
-- statement:
--   The Global Theory construction uses the weierstrass system add const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L108-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L108-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair Bornology
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)

theorem GlobalTheory.weierstrass_system_add_const (c : ℂ) {z : ℂ} (hz : z + c ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, HasDerivAt (fun t ↦ ℘[L] (t + c)) (℘'[L] (w + c)) w ∧
      HasDerivAt (fun t ↦ ℘'[L] (t + c)) (6 * ℘[L] (w + c) ^ 2 - L.g₂ / 2) w := by sorry
