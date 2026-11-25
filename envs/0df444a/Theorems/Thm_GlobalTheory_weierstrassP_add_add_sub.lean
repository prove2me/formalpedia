-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassP_add_add_sub
-- name    : GlobalTheory.weierstrassP_add_add_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:50.560443+00:00
-- url     : https://prove2.me/theorems/ed3ff65c-138f-439a-adf1-86f8f3780346
-- title:
--   Global Theory: weierstrass P add add sub
-- statement:
--   The Global Theory construction uses the weierstrass P add add sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L307-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L307-L324

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

theorem GlobalTheory.weierstrassP_add_add_sub {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) + ℘[L] (z - w) - 2 * ℘[L] w =
      (6 * ℘[L] w ^ 2 - L.g₂ / 2) / (℘[L] z - ℘[L] w) + ℘'[L] w ^ 2 / (℘[L] z - ℘[L] w) ^ 2 := by sorry
