-- Prove2me | Theorems.Thm_GlobalTheory_Lin_Repulsion_one_le_ord
-- name    : GlobalTheory.Lin.Repulsion.one_le_ord
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:06:17.131868+00:00
-- url     : https://prove2.me/theorems/887e86e7-37ff-44ba-9a00-303123cf08c6
-- title:
--   Repulsion: one le ord
-- statement:
--   The Repulsion construction uses the one le ord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L10-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L10-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion

theorem GlobalTheory.Lin.Repulsion.one_le_ord {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ} (hw : w ≠ 1)
    (h0 : LFunction χ w = 0) : 1 ≤ ord χ w := by sorry
