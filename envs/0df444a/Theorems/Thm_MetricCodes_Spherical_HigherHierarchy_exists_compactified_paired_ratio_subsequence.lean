-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_compactified_paired_ratio_subsequence
-- name    : MetricCodes.Spherical.HigherHierarchy.exists_compactified_paired_ratio_subsequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/72ed27a0-f32f-48e2-ac58-1f226855ec94
-- title:
--   MetricCodes.Spherical.HigherHierarchy.exists_compactified_paired_ratio_subsequence
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
open Filter Topology
open scoped Topology

theorem MetricCodes.Spherical.HigherHierarchy.exists_compactified_paired_ratio_subsequence
    {r : ℕ}
    (a : ℕ → Fin (r + 1) → ℝ) (b : ℕ → Fin r → ℝ)
    {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C) :
    ∃ (d : Fin r → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i, Tendsto (fun n => a (φ n) i.castSucc) atTop atTop →
        0 < d i) ∧
      (∀ i, Tendsto (fun n => a (φ n) i.castSucc) atTop atTop →
        Tendsto (fun n =>
          quadraticCoordinate (b (φ n) i) /
            quadraticCoordinate (a (φ n) i.castSucc))
          atTop (nhds (d i ^ 2))) := by sorry
