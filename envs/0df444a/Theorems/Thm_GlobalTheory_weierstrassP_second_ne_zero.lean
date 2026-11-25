-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassP_second_ne_zero
-- name    : GlobalTheory.weierstrassP_second_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:37.4558+00:00
-- url     : https://prove2.me/theorems/2ac2460d-a92a-4481-bd07-925f85e148a5
-- title:
--   Global Theory: weierstrass P second ne zero
-- statement:
--   The Global Theory construction uses the weierstrass P second ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L330-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L330-L341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassPAddOfNeOfDerivNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter PeriodPair WeierstrassCurve
open scoped Topology
noncomputable section
open GlobalTheory
variable (L : PeriodPair)
open Filter PeriodPair WeierstrassCurve
open scoped Topology
variable (L : PeriodPair)

theorem GlobalTheory.weierstrassP_second_ne_zero {w : ℂ} (hw : w ∉ L.lattice)
    (h : ℘'[L] w = 0) : 6 * ℘[L] w ^ 2 - L.g₂ / 2 ≠ 0 := by sorry
