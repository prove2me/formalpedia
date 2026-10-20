-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_bounded_hierarchy_subsequence
-- name    : MetricCodes.Spherical.HigherHierarchy.exists_compactified_bounded_hierarchy_subsequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:42.425795+00:00
-- url     : https://prove2.me/theorems/d15043e4-0fb1-482c-80af-9235240cf72f
-- title:
--   MetricCodes.Spherical.HigherHierarchy.exists_compactified_bounded_hierarchy_subsequence
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
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.exists_compactified_bounded_hierarchy_subsequence {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ k, Interlacing (a k) (b k))
    (hbound : ∀ k, Phi (a k) (b k) ≤ C) :
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (φ : ℕ → ℕ),
      StrictMono φ ∧ L ∈ Set.Icc (0 : ℝ) C ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (a (φ k) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto (fun k => compactifiedHierarchyCoordinate (b (φ k) i))
        atTop (nhds (B i))) ∧
      (∀ i : Fin r, A i.castSucc ≤ B i ∧ B i ≤ A i.succ) ∧
      0 < A (Fin.last r) ∧
      Tendsto (fun k => Phi (a (φ k)) (b (φ k)))
        atTop (nhds L) := by sorry
