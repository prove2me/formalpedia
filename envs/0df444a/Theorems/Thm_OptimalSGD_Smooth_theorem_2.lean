-- Prove2me | Theorems.Thm_OptimalSGD_Smooth_theorem_2
-- name    : OptimalSGD.Smooth.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:54.973375+00:00
-- url     : https://prove2.me/theorems/7689db5c-057d-48e7-8996-5202e63ae6f3
-- title:
--   Theorem 2 — averaged iterate: $\mathbb E[F(\bar w_T) - F(w^*)] \le 16\mu G^2/(\lambda^2 T)$ for $F$ smooth at $w^*$
-- statement:
--   **Setting.** Let $W \subseteq \mathbb R^d$ be closed and convex with $0 \in W$, let $\lambda > 0$, and let $F$ be $\lambda$-strongly convex on $W$ with a minimizer $w^* \in W$ over $W$. Assume $F$ is $\mu$-smooth with respect to $w^*$ for some $\mu \ge 0$:
--   $$F(w) - F(w^*) \le \frac{\mu}{2}\|w - w^*\|^2 \qquad (w \in W).$$
--   Let $g$ be a measurable stochastic subgradient oracle for $F$ relative to $W$ under a probability distribution $D$ (the mean $\mathbb E_z[g(w,z)]$ is a subgradient of $F$ at $w$ relative to $W$), with $\mathbb E_z\|g(w,z)\|^2 \le G^2$ for every $w \in W$. Projected SGD with $\eta_t = 1/(\lambda t)$ starts at $w_1 = 0$ and sets $w_{t+1} = \Pi_W(w_t - \eta_t g(w_t, z_t))$ with $z_t \sim D$ i.i.d.; its averaged output is $\bar w_T = (w_1 + \dots + w_T)/T$.
--
--   **Statement.** For every $T \ge 1$, $F(\bar w_T)$ is integrable and
--   $$\mathbb E\big[F(\bar w_T) - F(w^*)\big] \ \le\ \frac{16\mu G^2}{\lambda^2 T}.$$
--
--   Without smoothness, the classical analysis of the averaged iterate gives only $O(\log T / T)$, and Theorem 4 of the paper shows that this logarithm cannot be removed in general. Under the one-sided condition (2) at the optimum, full averaging attains the optimal $O(1/T)$ rate.
--
--   **Formalization Note** The space is $\mathbb R^d$ (`UnderstandingML.Vec d`) in place of a Hilbert space. $\bar w_T$ is `UnderstandingML.sgdStrongAverage lam W g S` with $S \sim D^T$ (`UnderstandingML.iidLaw D T`); the last draw $z_T$ is not used. The expectation is a Bochner integral and its integrability is part of the conclusion. Subgradients are relative to $W$; $W$ closed makes the projection exist; $0 \in W$ is the paper's initialization; $\mu \ge 0$ is the paper's tacit sign convention.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 4, Theorem 2 (proof App. B.3, p. 15)

import Definitions.Def_OptimalSGD_Smooth_Model
import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

namespace OptimalSGD.Smooth

/-- **Theorem 2** (arXiv:1109.5647v7, p. 4; proof App. B.3, p. 15). Suppose `F` is `λ`-strongly
convex and `µ`-smooth with respect to `w*` over a convex set `W`, and that `E[‖ĝₜ‖²] ≤ G²`. Then
with `ηₜ = 1/(λt)`, for any `T ≥ 1`, the average `w̄_T = (w₁ + … + w_T)/T` satisfies
`E[F(w̄_T) − F(w*)] ≤ 16µG²/(λ²T)`; `F(w̄_T)` is integrable. -/
theorem theorem_2 {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (G : ℝ) (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {μ : ℝ} (hμ : 0 ≤ μ) (hsmooth : IsSmoothWrt W F μ wstar)
    (T : ℕ) (hT : 1 ≤ T) :
    Integrable (fun S : Fin T → Z => F (sgdStrongAverage lam W g S)) (iidLaw D T) ∧
      (∫ S : Fin T → Z, F (sgdStrongAverage lam W g S) ∂(iidLaw D T)) - F wstar ≤
        16 * μ * G ^ 2 / (lam ^ 2 * T) := by sorry

end OptimalSGD.Smooth
