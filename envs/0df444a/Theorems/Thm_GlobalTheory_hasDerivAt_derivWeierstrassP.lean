-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_derivWeierstrassP
-- name    : GlobalTheory.hasDerivAt_derivWeierstrassP
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:48.498457+00:00
-- url     : https://prove2.me/theorems/2f215795-a8c0-41de-8cb6-e1384abace93
-- title:
--   Global Theory: has Deriv At deriv Weierstrass P
-- statement:
--   The Global Theory construction uses the has Deriv At deriv Weierstrass P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L44-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L44-L73

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

theorem GlobalTheory.hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by sorry
