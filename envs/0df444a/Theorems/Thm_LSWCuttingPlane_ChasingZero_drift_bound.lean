-- Prove2me | Theorems.Thm_LSWCuttingPlane_ChasingZero_drift_bound
-- name    : LSWCuttingPlane.ChasingZero.drift_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:42.973161+00:00
-- url     : https://prove2.me/theorems/168a8c21-3072-4349-84d8-033026558e3a
-- title:
--   Proof of Theorem 34, p. 43 — one-step drift: E Φ(x⃗ + Δ⃗) ≤ Φ(x⃗) + α²e^{αc}c²η for a mean-zero step with ‖Δ⃗‖₂ ≤ c
-- statement:
--   Let $m\ge1$, $c>0$ and $\alpha\ge0$. Let $\mathcal D$ be a probability distribution on $\mathbb R^m$ with mean $\mathbb E_{\mathcal D}\vec\Delta=\vec 0$ and $\|\vec\Delta\|_2\le c$ for $\mathcal D$-almost every $\vec\Delta$. For a point $\vec x\in\mathbb R^m$ write
--   $$\Phi(\vec x)=\sum_i e^{\alpha x_i}+\sum_i e^{-\alpha x_i},\qquad \eta=\max\Big(\max_i e^{\alpha x_i},\ \max_i e^{-\alpha x_i}\Big).$$
--   Then
--   $$\mathbb E_{\vec\Delta\sim\mathcal D}\,\Phi(\vec x+\vec\Delta)\le\Phi(\vec x)+\alpha^2e^{\alpha c}c^2\eta.$$
--
--   This is the expected increase of the potential caused by one move of the stochastic adversary in the chasing $\vec 0$ game, before the player responds; it is the inequality the proof of Theorem 34 obtains for $\vec x=\vec x^{(k)}$ and $\mathcal D=\mathcal D^{(k)}$.
--
--   **Formalization Note** $\mathcal D$ is a probability measure `ν` on `Fin m → ℝ`; "$\|\vec\Delta\|_2\le c$ for all $\vec\Delta\in\mathcal D$" is the almost-sure bound $\sum_i\Delta_i^2\le c^2$ (Euclidean norm, not Lean's sup norm), and the mean condition is $\int\Delta_i\,d\nu=0$ for every coordinate. All integrands are continuous and bounded on the support, so they are integrable. The hypothesis $\alpha\ge0$ is added: the page bounds $e^{\alpha\|\vec\Delta\|_\infty}$ by $e^{\alpha c}$, which needs it, and the $\alpha$ chosen later is positive. $c>0$ is Algorithm 4's standing constant.
-- source:
--   Lee, Sidford, Wong, A Faster Cutting Plane Method and its Implications for Combinatorial and Convex Optimization, arXiv:1508.04874v2, p. 43, proof of Theorem 34, display defining η^(k)

import Mathlib
import Definitions.Def_LSWCuttingPlane_ChasingZero_Setting

open MeasureTheory

namespace LSWCuttingPlane.ChasingZero

/-- Proof of Theorem 34, p. 43: for a distribution `ν` of steps `Δ⃗ ∈ ℝ^m` with mean `0⃗` and
`‖Δ⃗‖₂ ≤ c` on its support, and any point `x⃗`,
`E_{Δ⃗∼ν} Φ(x⃗ + Δ⃗) ≤ Φ(x⃗) + α² e^{αc} c² η`. -/
theorem drift_bound {m : ℕ} [NeZero m] (ν : Measure (Fin m → ℝ)) [IsProbabilityMeasure ν]
    (c α : ℝ) (hc : 0 < c) (hα : 0 ≤ α) (x : Fin m → ℝ)
    (hnorm : ∀ᵐ Δ ∂ν, ∑ i, (Δ i) ^ 2 ≤ c ^ 2)
    (hmean : ∀ i, ∫ Δ, Δ i ∂ν = 0) :
    ∫ Δ, Phi α (x + Δ) ∂ν ≤ Phi α x + α ^ 2 * Real.exp (α * c) * c ^ 2 * eta α x := by sorry

end LSWCuttingPlane.ChasingZero
