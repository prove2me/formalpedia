-- Prove2me | Theorems.Thm_GlobalTheory_T_one_sub_re_ge_of_exceptional_zero_repulsion
-- name    : GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:54:19.622621+00:00
-- url     : https://prove2.me/theorems/619ba4fd-c2d1-4095-91e6-19321b44c59d
-- title:
--   T: one sub re ge of exceptional zero repulsion
-- statement:
--   The T construction uses the one sub re ge of exceptional zero repulsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RepulsionStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/RepulsionStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RepulsionStatement
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

theorem GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (β L : ℝ) (ρ : ℂ), χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β < 1 → 1 / 2 ≤ β → LFunction χ₁ β = 0 → LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re < 1 → (χ ≠ χ₁ ∨ ρ ≠ β ∨ 2 ≤ ord χ₁ β) → Real.log (q * (|ρ.im| + 2)) ≤ L → c * Real.log (c / ((1 - β) * L)) / L ≤ 1 - ρ.re := by sorry
