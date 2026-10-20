-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_forward_residual_entropy_of_closure_sequence
-- name    : MetricCodes.Spherical.HigherHierarchy.exists_forward_residual_entropy_of_closure_sequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:49.086537+00:00
-- url     : https://prove2.me/theorems/08b45f73-2345-4fd1-8df7-b253c38339b8
-- title:
--   MetricCodes.Spherical.HigherHierarchy.exists_forward_residual_entropy_of_closure_sequence
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

theorem MetricCodes.Spherical.HigherHierarchy.exists_forward_residual_entropy_of_closure_sequence
    {r : ℕ} {s R : ℝ}
    (u : ℕ → ℝ)
    (a : ℕ → Fin (r + 1) → ℝ)
    (b : ℕ → Fin r → ℝ)
    (hu : Tendsto u atTop (nhds s))
    (hinter : ∀ n, Interlacing (a n) (b n))
    (hgap : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hPhi : ∀ n, Phi (a n) (b n) ≤ R + 1 / ((n : ℝ) + 1)) :
    ∃ (L : ℝ) (A : Fin (r + 1) → ℝ) (B : Fin r → ℝ)
      (d : Fin r → ℝ) (φ : ℕ → ℕ)
      (k j : ℕ) (hkj : k + j = r)
      (q : ℕ) (a₀ : Fin (q + 1) → ℝ) (b₀ : Fin q → ℝ)
      (c : ℝ),
      StrictMono φ ∧
      0 ≤ L ∧ L ≤ R ∧
      (∀ i, A i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, B i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (a (φ n) i))
        atTop (nhds (A i))) ∧
      (∀ i, Tendsto
        (fun n => compactifiedHierarchyCoordinate (b (φ n) i))
        atTop (nhds (B i))) ∧
      Tendsto (fun n => u (φ n)) atTop (nhds s) ∧
      (∀ n, u (φ n) < 2 * Gamma (a (φ n)) (b (φ n))) ∧
      Tendsto (fun n => Phi (a (φ n)) (b (φ n))) atTop (nhds L) ∧
      (∀ i, d i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, Tendsto
        (fun n => b (φ n) i / a (φ n) i.castSucc)
        atTop (nhds (d i))) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 →
        0 < d i ∧
        Tendsto
          (fun n => quadraticCoordinate (b (φ n) i) /
            quadraticCoordinate (a (φ n) i.castSucc))
          atTop (nhds (d i ^ 2))) ∧
      q ≤ j ∧ Interlacing a₀ b₀ ∧
      (∀ i : Fin r, i.val < k → A i.castSucc = 0 ∧ B i = 0) ∧
      (∀ i : Fin r, A i.castSucc = 0 ↔ i.val < k) ∧
      (∀ i, compactifiedAmbientSuffix hkj A i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i, compactifiedStabilizerSuffix hkj B i ∈ Set.Ioc (0 : ℝ) 1) ∧
      (∀ i : Fin j,
        compactifiedAmbientSuffix hkj A i.castSucc ≤
          compactifiedStabilizerSuffix hkj B i ∧
        compactifiedStabilizerSuffix hkj B i ≤
          compactifiedAmbientSuffix hkj A i.succ) ∧
      Phi a₀ b₀ =
        Phi (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) ∧
      (∀ t : ℝ, 0 < t →
        hierarchyStieltjesRatio
          (fun i => (compactifiedAmbientSuffix hkj A i)⁻¹ - 1)
          (fun i => (compactifiedStabilizerSuffix hkj B i)⁻¹ - 1) t =
            hierarchyStieltjesRatio a₀ b₀ t) ∧
      c = ∏ i ∈ Finset.univ.filter (fun i : Fin r => i.val < k), d i ∧
      0 < c ∧ c ≤ 1 ∧ (c < 1 → q < r) ∧
      L = Phi a₀ b₀ - Real.logb 2 c := by sorry
