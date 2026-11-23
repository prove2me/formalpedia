-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_weierstrassP
-- name    : GlobalTheory.hasDerivAt_weierstrassP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:54.082157+00:00
-- url     : https://prove2.me/theorems/b4a6cbef-02b0-4a45-9385-a06e183a4962
-- title:
--   Global Theory: has Deriv At weierstrass P
-- statement:
--   The Global Theory construction uses the has Deriv At weierstrass P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L41-L42

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

theorem GlobalTheory.hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by sorry
