-- Prove2me | Theorems.Thm_GlobalTheory_analyticAt_weierstrassP_add
-- name    : GlobalTheory.analyticAt_weierstrassP_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:31.239542+00:00
-- url     : https://prove2.me/theorems/f9f95812-5ca9-4d71-b14f-27973273dd09
-- title:
--   Global Theory: analytic At weierstrass P add
-- statement:
--   The Global Theory construction uses the analytic At weierstrass P add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L119-L121

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

theorem GlobalTheory.analyticAt_weierstrassP_add (c : ℂ) {z : ℂ} (hz : z + c ∉ L.lattice) :
    AnalyticAt ℂ (fun t ↦ ℘[L] (t + c)) z := by sorry
