-- Prove2me | Theorems.Thm_GlobalTheory_Hk_tsum_prod_weight_approx
-- name    : GlobalTheory.Hk.tsum_prod_weight_approx
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:36:35.440723+00:00
-- url     : https://prove2.me/theorems/d0644a85-7118-4791-bbc7-e5b1bdaf4716
-- title:
--   Hk: tsum prod weight approx
-- statement:
--   The Hk construction uses the tsum prod weight approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ThetaQForm.lean#L9-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ThetaQForm.lean#L9-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SummableExpNegMulSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ThetaQForm
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

theorem GlobalTheory.Hk.tsum_prod_weight_approx {ι κ : Type} (u : ι → κ → ℝ) (w : κ → ℝ) (A a C c : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hu0 : ∀ m k, 0 ≤ u m k) (hw0 : ∀ k, 0 ≤ w k)
    (hu : ∀ k, Summable (fun m => u m k) ∧ |∑' m, u m k - A| ≤ A * a)
    (hw : Summable w ∧ |∑' k, w k - C| ≤ C * c) :
    Summable (fun v : ι × κ => u v.1 v.2 * w v.2) ∧
      |∑' v : ι × κ, u v.1 v.2 * w v.2 - A * C| ≤ A * C * (a + c + a * c) := by sorry
