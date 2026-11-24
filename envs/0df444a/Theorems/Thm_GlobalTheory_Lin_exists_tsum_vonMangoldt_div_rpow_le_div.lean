-- Prove2me | Theorems.Thm_GlobalTheory_Lin_exists_tsum_vonMangoldt_div_rpow_le_div
-- name    : GlobalTheory.Lin.exists_tsum_vonMangoldt_div_rpow_le_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:06:41.780027+00:00
-- url     : https://prove2.me/theorems/582321cf-c160-4905-a7fa-cc35063be05f
-- title:
--   Lin: exists tsum von Mangoldt div rpow le div
-- statement:
--   The Lin construction uses the exists tsum von Mangoldt div rpow le div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsTsumVonMangoldtDivRpowLeDiv.lean#L12-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsTsumVonMangoldtDivRpowLeDiv.lean#L12-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsTsumVonMangoldtDivRpowLeDiv
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
open GlobalTheory GlobalTheory.Lin
open ArithmeticFunction.vonMangoldt (residueClass LFunctionResidueClassAux LFunctionResidueClassAux_real
  eqOn_LFunctionResidueClassAux residueClass_apply_zero continuousOn_LFunctionResidueClassAux
  abscissaOfAbsConv_residueClass_le_one)

theorem GlobalTheory.Lin.exists_tsum_vonMangoldt_div_rpow_le_div :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      Summable (fun n : ℕ => Λ n / (n : ℝ) ^ (1 + s)) ∧
        ∑' n : ℕ, Λ n / (n : ℝ) ^ (1 + s) ≤ C / s := by sorry
