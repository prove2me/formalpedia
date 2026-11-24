-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_Red_sm_neg
-- name    : GlobalTheory.UnitDiscAlg.Red.sm_neg
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:38:17.16495+00:00
-- url     : https://prove2.me/theorems/1015513f-2562-414a-8ad9-dfe56bfbcfd7
-- title:
--   Red: sm neg
-- statement:
--   The Red construction uses the sm neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommutingIntegralMatrixDecompose.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixTopnilStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommutingIntegralMatrixDecompose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitDiscAlg
open GlobalTheory GlobalTheory.UnitDiscAlg GlobalTheory.UnitDiscAlg.Red
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem GlobalTheory.UnitDiscAlg.Red.sm_neg {x : Matrix (Fin n) (Fin n) E} (hx : Sm x) : Sm (-x) := by sorry
