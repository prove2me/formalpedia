-- Prove2me | Theorems.Thm_GlobalTheory_PrimeMeanValue_prime_mean_value
-- name    : GlobalTheory.PrimeMeanValue.prime_mean_value
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:56:41.110938+00:00
-- url     : https://prove2.me/theorems/2a40534e-5b5d-4b7d-bf00-4097a8647971
-- title:
--   Prime Mean Value: prime mean value
-- statement:
--   The Prime Mean Value construction uses the prime mean value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeMeanValueCharactersTwistIntegralLe.lean#L179-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PrimeMeanValueCharactersTwistIntegralLe.lean#L179-L258

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

theorem GlobalTheory.PrimeMeanValue.prime_mean_value : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T →
    (2 * q * T) ^ 2 ≤ N → ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
      ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
      C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by sorry
