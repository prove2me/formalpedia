-- Prove2me | Theorems.Thm_GlobalTheory_ZeroWindow_count_zeros_window
-- name    : GlobalTheory.ZeroWindow.count_zeros_window
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:22.241599+00:00
-- url     : https://prove2.me/theorems/b7ffd85c-ea4b-4c82-9608-d1e42f13ebf2
-- title:
--   Zero Window: count zeros window
-- statement:
--   The Zero Window construction uses the count zeros window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinsumMemLeOfSubset.lean#L43-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/FinsumMemLeOfSubset.lean#L43-L106

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FinsumMemLeOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ZeroWindow
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem GlobalTheory.ZeroWindow.count_zeros_window : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N]
    (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ t : ℝ,
    {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}.Finite ∧
    ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) ≤ C * Real.log (N * (|t| + 2)) := by sorry
