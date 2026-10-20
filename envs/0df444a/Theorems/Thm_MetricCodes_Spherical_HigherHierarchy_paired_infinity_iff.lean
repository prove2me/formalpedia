-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_paired_infinity_iff
-- name    : MetricCodes.Spherical.HigherHierarchy.paired_infinity_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/bd0ad83d-9c32-454a-a562-8b166065063a
-- title:
--   MetricCodes.Spherical.HigherHierarchy.paired_infinity_iff
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
open scoped BigOperators Topology

theorem MetricCodes.Spherical.HigherHierarchy.paired_infinity_iff
    {r : ℕ}
    {a : ℕ → Fin (r + 1) → ℝ} {b : ℕ → Fin r → ℝ}
    {A : Fin (r + 1) → ℝ} {B : Fin r → ℝ} {φ : ℕ → ℕ} {C : ℝ}
    (h : ∀ n, Interlacing (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ C)
    (hA : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
      atTop (nhds (A i)))
    (hB : ∀ i, Tendsto
      (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
      atTop (nhds (B i)))
    (hAnonneg : ∀ i, 0 ≤ A i)
    (hBnonneg : ∀ i, 0 ≤ B i) :
    ∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0 := by sorry
