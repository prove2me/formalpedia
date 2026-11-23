-- Prove2me | Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
-- name    : GlobalTheory.derivWeierstrassP_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:57:21.155793+00:00
-- url     : https://prove2.me/theorems/79b22f6c-df8d-4de7-9faa-11c5e71cd91a
-- title:
--   Global Theory: deriv Weierstrass P eq zero iff
-- statement:
--   The Global Theory construction uses the deriv Weierstrass P eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassPAddOfNeOfDerivNeZero.lean#L158-L166

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

theorem GlobalTheory.derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ z + z ∈ L.lattice := by sorry
