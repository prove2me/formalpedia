-- Prove2me | Theorems.Thm_GlobalTheory_SmallDiscZeros_few_zeros
-- name    : GlobalTheory.SmallDiscZeros.few_zeros
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:18:15.295892+00:00
-- url     : https://prove2.me/theorems/b6db930f-378d-41b5-a9ec-8e2825bc5f8c
-- title:
--   Small Disc Zeros: few zeros
-- statement:
--   The Small Disc Zeros construction uses the few zeros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLFewZerosSmallDisc.lean#L98-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLFewZerosSmallDisc.lean#L98-L203

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZerosStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDisc
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
open GlobalTheory GlobalTheory.SmallDiscZeros
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open scoped Classical

theorem GlobalTheory.SmallDiscZeros.few_zeros : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (_root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ _root_.GlobalTheory.Lin.zerosDisc χ (1 + t * I) r, (_root_.GlobalTheory.Lin.ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by sorry
