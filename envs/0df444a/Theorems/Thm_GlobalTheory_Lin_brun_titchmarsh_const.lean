-- Prove2me | Theorems.Thm_GlobalTheory_Lin_brun_titchmarsh_const
-- name    : GlobalTheory.Lin.brun_titchmarsh_const
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:07:03.098349+00:00
-- url     : https://prove2.me/theorems/eac61325-5614-455f-8eeb-2db5e3d88b33
-- title:
--   Lin: brun titchmarsh const
-- statement:
--   The Lin construction uses the brun titchmarsh const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BrunTitchmarshExistsConst.lean#L48-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/BrunTitchmarshExistsConst.lean#L48-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ArithmeticLargeSieveOneResidueClassPerPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BrunTitchmarshExistsConst
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

theorem GlobalTheory.Lin.brun_titchmarsh_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by sorry
