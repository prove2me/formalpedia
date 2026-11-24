-- Prove2me | Theorems.Thm_GlobalTheory_Lin_Repulsion_summable_der
-- name    : GlobalTheory.Lin.Repulsion.summable_der
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:16.046203+00:00
-- url     : https://prove2.me/theorems/e4acf2c0-dea7-4f50-a33e-b78de09e6271
-- title:
--   Repulsion: summable der
-- statement:
--   The Repulsion construction uses the summable der property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L80-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L80-L105

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

theorem GlobalTheory.Lin.Repulsion.summable_der (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ) (t : ℝ) :
    Summable fun n : ℕ => ((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((2 : ℂ) + t * I)) := by sorry
