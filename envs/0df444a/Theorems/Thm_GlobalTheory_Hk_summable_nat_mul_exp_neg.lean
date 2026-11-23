-- Prove2me | Theorems.Thm_GlobalTheory_Hk_summable_nat_mul_exp_neg
-- name    : GlobalTheory.Hk.summable_nat_mul_exp_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:00:36.828958+00:00
-- url     : https://prove2.me/theorems/aa250529-9b43-49ca-9ab2-fe0973a8cbc3
-- title:
--   Hk: summable nat mul exp neg
-- statement:
--   The Hk construction uses the summable nat mul exp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L142-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExpSumBounds.lean#L142-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExpSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk

theorem GlobalTheory.Hk.summable_nat_mul_exp_neg {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => (n : ℝ) * Real.exp (-(t * n))) := by sorry
