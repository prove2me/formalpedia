-- Prove2me | Theorems.Thm_GlobalTheory_GoodHeight_local_formula
-- name    : GlobalTheory.GoodHeight.local_formula
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:56:43.597443+00:00
-- url     : https://prove2.me/theorems/30d4a5c0-f87e-4acc-abda-85072a7990bd
-- title:
--   Good Height: local formula
-- statement:
--   The Good Height construction uses the local formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L93-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsBoundRight.lean#L93-L148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight

theorem GlobalTheory.GoodHeight.local_formula : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 2 ≤ |s.im| → LFunction χ s ≠ 0 →
    ∃ Z : Finset ℂ, (∀ w, w ∈ Z ↔ ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ w ≠ 1 ∧ LFunction χ w = 0) ∧
      ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℝ) ≤ C * Real.log (N * (|s.im| + 2)) ∧
      ‖deriv (LFunction χ) s / LFunction χ s
        - ∑ w ∈ Z, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖
        ≤ C * Real.log (N * (|s.im| + 2)) := by sorry
