-- Prove2me | Theorems.Thm_OLPRegret_lemma_2
-- name    : OLPRegret.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:02:45.39847+00:00
-- url     : https://prove2.me/theorems/ad4f91bb-6c77-454a-9b12-20697dfde6be
-- title:
--   Lemma 2 — limiting shadow prices are locally differentiable in the resource vector
-- statement:
--   Under Assumptions 2–6, there is $\delta>0$ such that for $b\in B_\delta(\beta)$ the function $\Lambda_\infty^b$ has a unique minimizer $y_\infty^b$ over $\mathbb R^m_+$, with $y_\infty^b>0$; the map $b\mapsto y_\infty^b$ is continuously differentiable and Lipschitz on $B_\delta(\beta)$, and
--   $$
--   \partial_by_\infty^b=-\ddot\Lambda_\infty(y_\infty^b)^{-1}.
--   $$
--
--   Differences from the source:
--   - reading: "if $b$ is sufficiently close to $\beta$ ... Lipschitz continuous" → one ball $B_\delta(\beta)$ for every clause, Lipschitz on that ball; reason: a $C^1$ map is Lipschitz on a small enough ball
--   - encoding: $\ddot\Lambda_\infty^{-1}$ → `ContinuousLinearMap.inverse` with an explicit invertibility clause; reason: `inverse` is $0$ on non-invertible maps; the clause excludes that
-- source:
--   Bray, arXiv:1912.08917v6, Lemma 2, p.20

import Mathlib
import Definitions.Def_OLPRegret_Assumptions

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Lemma 2, p.20. If `b` is sufficiently close to `β`, then `Λ∞ᵇ` has a
unique minimizer `y∞ᵇ > 0`, which is continuously differentiable in `b` with
`∂y∞ᵇ/∂b = −Λ̈∞(y∞ᵇ)⁻¹`, and Lipschitz.

**Formalization Note** "and hence Lipschitz continuous": on a small enough ball. `yInf` is the unique
minimizer on that ball, and the invertibility clause rules out the junk value of
`ContinuousLinearMap.inverse`. -/
theorem lemma_2 {m : ℕ} (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ L : NNReal,
      (∀ b ∈ Metric.ball β δ,
        (∃! y, IsMinimizer (LambdaInf μ b) y) ∧
        IsMinimizer (LambdaInf μ b) (yInf μ b) ∧ (∀ i, 0 < yInf μ b i) ∧
        (hessInf μ (yInf μ b)).IsInvertible ∧
        HasFDerivAt (yInf μ) (-(hessInf μ (yInf μ b)).inverse) b) ∧
      ContDiffOn ℝ 1 (yInf μ) (Metric.ball β δ) ∧
      LipschitzOnWith L (yInf μ) (Metric.ball β δ) := by sorry

end OLPRegret
