-- Prove2me | Theorems.Thm_GlobalTheory_T_dirichletL_few_zeros_small_disc
-- name    : GlobalTheory.T.dirichletL_few_zeros_small_disc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:31:45.020111+00:00
-- url     : https://prove2.me/theorems/b92f1b5f-1b62-462d-bf43-830316d65976
-- title:
--   T: dirichlet L few zeros small disc
-- statement:
--   The T construction uses the dirichlet L few zeros small disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLFewZerosSmallDiscStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLFewZerosSmallDiscStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDisc
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDiscStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.dirichletL_few_zeros_small_disc : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (1 + t * I) r, (ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by sorry
