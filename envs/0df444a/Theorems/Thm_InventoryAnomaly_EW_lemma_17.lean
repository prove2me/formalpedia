-- Prove2me | Theorems.Thm_InventoryAnomaly_EW_lemma_17
-- name    : InventoryAnomaly.EW.lemma_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:59.629899+00:00
-- url     : https://prove2.me/theorems/414d22ed-e21e-4530-a0c9-8c6301ec6733
-- title:
--   Lemma 17, p. 44 (square case d₁ = d₂) — quantitative inverse function bound ‖F(θ) − F(θ*)‖ ≤ δ ⟹ ‖θ − θ*‖ ≤ 2C₂δ
-- statement:
--   Let $F:\Theta\subset\mathbb R^D\to\mathbb R^D$ be continuously differentiable and injective on $\Theta$, let $\theta^*\in\Theta$ and $C_1,C_2,\delta\in\mathbb R$, and assume
--   1. $B_{2C_2\delta}(\theta^*)=\{\theta:\|\theta-\theta^*\|\le 2C_2\delta\}\subset\Theta$;
--   2. $\|J_F(\theta)-J_F(\theta^*)\|_{\max}\le C_1\|\theta-\theta^*\|$ for $\theta\in B_{2C_2\delta}(\theta^*)$;
--   3. $J_F(\theta^*)$ is invertible with $\|J_F(\theta^*)^{-1}\|_2\le C_2$;
--   4. $2\sqrt{D\cdot D}\,C_1C_2^2\delta<1/2$.
--
--   Then for every $\theta\in\Theta$,
--   $$\|F(\theta)-F(\theta^*)\|\le\delta\ \Longrightarrow\ \|\theta-\theta^*\|\le 2C_2\delta .\qquad(33)$$
--
--   It turns closeness of the moments, $F(\hat\theta)\approx F(\theta^*)$, into closeness of the parameters.
--
--   **Formalization Note.** The paper states the lemma for $F:\mathbb R^{d_1}\to\mathbb R^{d_2}$; it is formalized for $d_1=d_2=D$, the case Lemma 1 uses ($T=d+1=\dim\theta$), because for $d_2>d_1$ the Jacobian has no two-sided inverse. $J_F$ is the Fréchet derivative of $F$ within $\Theta$ (one-sided at boundary points of $\Theta$, where $F$ is only assumed $C^1$ on $\Theta$), $\|\cdot\|_2$ the operator norm, and $\|\cdot\|_{\max}$ the largest matrix entry $|J(e_j)_i|$. $\theta^*\in\Theta$ is stated explicitly.
-- source:
--   Farias, Li & Peng, Fixing Inventory Inaccuracies at Scale, arXiv:2006.13126v3, p. 44, Lemma 17, eq. (33)

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InventoryAnomaly.EW

theorem lemma_17 {D : ℕ} (F : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D))
    (Θ : Set (EuclideanSpace ℝ (Fin D))) (θs : EuclideanSpace ℝ (Fin D)) (C1 C2 δ : ℝ)
    (hF : ContDiffOn ℝ 1 F Θ) (hinj : Set.InjOn F Θ) (hθs : θs ∈ Θ)
    (hball : Metric.closedBall θs (2 * C2 * δ) ⊆ Θ)
    (hJ : ∀ θ ∈ Metric.closedBall θs (2 * C2 * δ), ∀ i j : Fin D,
      |(fderivWithin ℝ F Θ θ - fderivWithin ℝ F Θ θs) (EuclideanSpace.single j 1) i| ≤ C1 * ‖θ - θs‖)
    (Jinv : EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D))
    (hJinv : Jinv.comp (fderivWithin ℝ F Θ θs) = ContinuousLinearMap.id ℝ _ ∧
      (fderivWithin ℝ F Θ θs).comp Jinv = ContinuousLinearMap.id ℝ _)
    (hC2 : ‖Jinv‖ ≤ C2) (hsmall : 2 * Real.sqrt (D * D) * C1 * C2 ^ 2 * δ < 1 / 2) :
    ∀ θ ∈ Θ, ‖F θ - F θs‖ ≤ δ → ‖θ - θs‖ ≤ 2 * C2 * δ := by sorry

end InventoryAnomaly.EW
