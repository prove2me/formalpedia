-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_succ_lt_of_compactified_positive_minimizer
-- name    : MetricCodes.Spherical.HigherHierarchy.levelRate_succ_lt_of_compactified_positive_minimizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:50.940664+00:00
-- url     : https://prove2.me/theorems/52e3ec62-3b8f-47a4-a9e1-7466af9711c0
-- title:
--   MetricCodes.Spherical.HigherHierarchy.levelRate_succ_lt_of_compactified_positive_minimizer
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section

theorem MetricCodes.Spherical.HigherHierarchy.levelRate_succ_lt_of_compactified_positive_minimizer
    {r j : ℕ} {s c : ℝ}
    {a : Fin (j + 1) → ℝ} {b : Fin j → ℝ}
    (hj : j ≤ r) (hc : 0 < c) (hc' : c ≤ 1)
    (hdrop : c < 1 → j < r)
    (h : Interlacing a b) (hlast : 0 < a (Fin.last j))
    (hfeasible : s ≤ 1 - c ^ 2 * (1 - 2 * Gamma a b))
    (hmin : levelRate r s = Phi a b - Real.logb 2 c)
    (htransfer : ∀ {k j' : ℕ}
      (A : Fin (j' + 1) → ℝ) (B : Fin j' → ℝ),
      Interlacing A B →
      s < 1 - c ^ 2 * (1 - 2 * Gamma A B) →
      ((c = 1 ∧ j' ≤ k) ∨ (c < 1 ∧ j' + 1 ≤ k)) →
      levelRate k s ≤ Phi A B - Real.logb 2 c) :
    levelRate (r + 1) s < levelRate r s := by sorry
