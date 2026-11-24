-- Prove2me | Theorems.Thm_GlobalTheory_Lin_Repulsion_norm_pow_sub_le
-- name    : GlobalTheory.Lin.Repulsion.norm_pow_sub_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:07:16.267605+00:00
-- url     : https://prove2.me/theorems/0cfaec0e-e414-468f-ad8c-5ac60840f5a1
-- title:
--   Repulsion: norm pow sub le
-- statement:
--   The Repulsion construction uses the norm pow sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L34-L47

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

theorem GlobalTheory.Lin.Repulsion.norm_pow_sub_le {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (j : ℕ) :
    ‖a ^ j - b ^ j‖ ≤ j * ‖a - b‖ := by sorry
