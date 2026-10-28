-- Prove2me | Theorems.Thm_MomentProblem_exists_dual_of_slater
-- name    : MomentProblem.exists_dual_of_slater
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T05:15:02.697471+00:00
-- url     : https://prove2.me/theorems/8ce11cf4-c6e1-4003-bc1b-aa1bd395de0f
-- title:
--   Duality for a moment problem: a bound on all feasible measures comes from a dual function
-- statement:
--   Let $X$ be a measurable space, $\iota$ a finite index type, $T \subseteq X$ measurable,
--   $\varphi : X \to \mathbb{R}^{\iota}$ measurable in each coordinate, $g : X \to \mathbb{R}$
--   measurable, and $B \subseteq \mathbb{R}^{\iota}$ a convex set of admissible moment vectors.
--   Suppose every finite measure $\mu$ supported in $T$ whose moment vector
--   $\bigl(\int \varphi_i \, d\mu\bigr)_i$ lies in $B$ satisfies $\int g \, d\mu \le p$, and suppose
--   the generalized Slater condition holds: $0$ is in the interior of the set of achievable moment
--   discrepancies $\bigl(\int \varphi_i \, d\mu\bigr)_i - s$ over such $\mu$ and $s \in B$. Then the
--   bound is witnessed by a dual vector:
--
--   $$
--   \exists\, \eta \in \mathbb{R}^{\iota}: \quad
--   g(x) \le \eta \cdot \varphi(x) \ \text{ for all } x \in T,
--   \qquad \eta \cdot s \le p \ \text{ for all } s \in B .
--   $$
--
--   A worst-case expectation over a set of measures described by moment conditions is an
--   infinite-dimensional linear program, and this is its dual: the pointwise majorization
--   $g \le \eta \cdot \varphi$ on $T$ replaces the quantification over measures entirely. It is the
--   step that turns a distributionally robust bound into a finite-dimensional condition, and the
--   Slater hypothesis is stated on the achievable discrepancies, which is what makes it checkable in
--   applications where $B$ encodes equalities as well as inequalities.
-- source:
--   A. Shapiro, On duality theory of conic linear problems, in Semi-Infinite Programming (Kluwer, 2001), 135-165. Carved from https://prove2.me/submissions/3c55ced4-4944-4de2-ba43-8110d2682db1, lines 3556-3636 (the goal proof of DRJointCC.Joint.theorem_3_6, which re-derives it inline; the same block appears in https://prove2.me/submissions/351d29f4-df20-4118-a8bc-25a1b62a5233 for DRJointCC.Individual.theorem_2_2)

import Mathlib

open MeasureTheory Matrix
open scoped ENNReal

theorem MomentProblem.exists_dual_of_slater {X : Type*} [MeasurableSpace X] {ι : Type*} [Fintype ι]
    (T : Set X) (hT : MeasurableSet T) (φ : X → ι → ℝ) (hφ : ∀ i, Measurable fun x => φ x i)
    (g : X → ℝ) (hg : Measurable g) (B : Set (ι → ℝ)) (hB : Convex ℝ B) (p : ℝ)
    (hp : ∀ μ : Measure X, IsFiniteMeasure μ → μ Tᶜ = 0 →
      (∀ i, Integrable (fun x => φ x i) μ) → Integrable g μ →
      (fun i => ∫ x, φ x i ∂μ) ∈ B → ∫ x, g x ∂μ ≤ p)
    (hslater : (0 : ι → ℝ) ∈ interior {u | ∃ μ : Measure X, IsFiniteMeasure μ ∧ μ Tᶜ = 0 ∧
      (∀ i, Integrable (fun x => φ x i) μ) ∧ Integrable g μ ∧
      ∃ s ∈ B, (fun i => ∫ x, φ x i ∂μ) - s = u}) :
    ∃ η : ι → ℝ, (∀ x ∈ T, g x ≤ η ⬝ᵥ φ x) ∧ ∀ s ∈ B, η ⬝ᵥ s ≤ p := by sorry
