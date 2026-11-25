-- Prove2me | Theorems.Thm_GlobalTheory_weierstrassP_add
-- name    : GlobalTheory.weierstrassP_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:38.536195+00:00
-- url     : https://prove2.me/theorems/2fb3a2bb-776a-453d-a9c2-66d303b1aced
-- title:
--   Global Theory: weierstrass P add
-- statement:
--   The Global Theory construction uses the weierstrass P add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L296-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/WeierstrassCurvePointOfLatticeAddOfGeneric.lean#L296-L301

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

theorem GlobalTheory.weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice)
    (hw : w ∉ L.lattice) (hne : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) := by sorry
