-- Prove2me | Theorems.Thm_GlobalTheory_PrimeMeanValue_kernel_integral
-- name    : GlobalTheory.PrimeMeanValue.kernel_integral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:56:01.093026+00:00
-- url     : https://prove2.me/theorems/644ae3e6-ad87-4f5f-b86b-be93642ce473
-- title:
--   Prime Mean Value: kernel integral
-- statement:
--   The Prime Mean Value construction uses the kernel integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeMeanValueCharactersTwistIntegralLe.lean#L29-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeMeanValueCharactersTwistIntegralLe.lean#L29-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IntegralNormSqLp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConstStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PrimeMeanValueCharactersTwistIntegralLe
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
open GlobalTheory GlobalTheory.PrimeMeanValue

theorem GlobalTheory.PrimeMeanValue.kernel_integral (n δ : ℝ) (hn : 0 < n) (hδ : 0 ≤ δ) :
    IntegrableOn (fun x : ℝ => if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) (Set.Ioi 0) ∧
    ∫ x in Set.Ioi (0 : ℝ), (if x < n ∧ n ≤ x * Real.exp δ then 1 / x else 0) = δ := by sorry
