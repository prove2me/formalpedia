-- Prove2me | Theorems.Thm_NonconvexDRS_ImageSmooth_lemma_2_1
-- name    : NonconvexDRS.ImageSmooth.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:38:25.698134+00:00
-- url     : https://prove2.me/theorems/2cd8a08e-9e67-409e-99c0-b407e35285bc
-- title:
--   Lemma 2.1, p. 6 — subdifferential characterization of smoothness: (2.4) on ∂h with ∂h ≠ ∅ gives L-smooth, σ-hypoconvex h
-- statement:
--   Let $h:\mathbb R^n\to\mathbb R$ be lower semicontinuous and such that its limiting subdifferential $\partial h(x)$ is nonempty for every $x\in\mathbb R^n$, and suppose there are $L\ge0$ and $\sigma\in[-L,L]$ such that
--   $$\sigma\|x_1-x_2\|^2\le\langle v_1-v_2,x_1-x_2\rangle\le L\|x_1-x_2\|^2\qquad\forall x_i\in\mathbb R^n,\ v_i\in\partial h(x_i),\ i=1,2.\qquad(2.4)$$
--   Then $h\in C^{1,1}(\mathbb R^n)$ is $L$-smooth and $\sigma$-hypoconvex: $h$ is differentiable, $\|\nabla h(x)-\nabla h(y)\|\le L\|x-y\|$ for all $x,y$, and $h-\frac\sigma2\|\cdot\|^2$ is convex.
--
--   This lemma is the final step of the proof of Theorem 5.13: in each case, the bounds obtained for the subgradients of $(Af)$ are exactly (2.4).
--
--   **Formalization Note** Lower semicontinuity of $h$ is added; it is necessary. With the limiting subdifferential of p. 6 (sequences $x^k\to x$ with $h(x^k)\to h(x)$), the step function $h(x)=-1$ for $x<0$, $h(x)=0$ for $x\ge0$ on $\mathbb R$ has $\partial h(x)=\{0\}$ for every $x$, so (2.4) holds with $L=\sigma=0$, yet $h$ is not differentiable. The proof cites [Rockafellar–Wets, Ex. 12.28, Cor. 9.19], which are for lsc functions. In Theorem 5.13 the lemma is applied to $(Af)$, which is lsc. $C^{1,1}$ is contained in `IsLSmooth`, which includes differentiability, and a Lipschitz gradient is continuous.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 6, Lemma 2.1 (2.4) (proof pp. 26–27)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ImageSmooth_Setting

open NonconvexSplitting.Shared
open scoped InnerProductSpace

namespace NonconvexDRS.ImageSmooth

/-- Lemma 2.1, p. 6 (subdifferential characterization of smoothness): if `h : ℝⁿ → ℝ` is lsc, has
nonempty limiting subdifferential everywhere, and for some `L ≥ 0`, `σ ∈ [-L, L]`,
`σ‖x₁ - x₂‖² ≤ ⟨v₁ - v₂, x₁ - x₂⟩ ≤ L‖x₁ - x₂‖²` for all `xᵢ` and `vᵢ ∈ ∂h(xᵢ)` (2.4), then `h` is
`L`-smooth and `σ`-hypoconvex. Lower semicontinuity is a necessary addition. -/
theorem lemma_2_1 {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ) (hlsc : LowerSemicontinuous h)
    (hne : ∀ x, (LimitingSubdiff (fun y => (h y : EReal)) x).Nonempty)
    (L σ : ℝ) (hL : 0 ≤ L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (h24 : ∀ (x₁ x₂ v₁ v₂ : EuclideanSpace ℝ (Fin n)),
      v₁ ∈ LimitingSubdiff (fun y => (h y : EReal)) x₁ →
      v₂ ∈ LimitingSubdiff (fun y => (h y : EReal)) x₂ →
      σ * ‖x₁ - x₂‖ ^ 2 ≤ ⟪v₁ - v₂, x₁ - x₂⟫_ℝ ∧ ⟪v₁ - v₂, x₁ - x₂⟫_ℝ ≤ L * ‖x₁ - x₂‖ ^ 2) :
    NonconvexDRS.DRS.IsLSmooth h L ∧ NonconvexDRS.DRS.IsHypoconvex h σ := by sorry

end NonconvexDRS.ImageSmooth
