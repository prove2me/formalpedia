-- Prove2me | Theorems.Thm_OptimalSGD_Smooth_theorem_1
-- name    : OptimalSGD.Smooth.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:53.182975+00:00
-- url     : https://prove2.me/theorems/a583cb1e-3c78-460e-984d-913406bf6f2f
-- title:
--   Theorem 1 — last iterate: $\mathbb E[F(w_T) - F(w^*)] \le 2\mu G^2/(\lambda^2 T)$ for $F$ smooth at $w^*$
-- statement:
--   **Setting.** As in Lemma 1: $W \subseteq \mathbb R^d$ closed and convex with $0 \in W$; $F$ $\lambda$-strongly convex on $W$ ($\lambda > 0$) with minimizer $w^* \in W$ over $W$; a measurable stochastic subgradient oracle $g$ relative to $W$ with $\mathbb E_z\|g(w,z)\|^2 \le G^2$ for all $w \in W$; projected SGD $w_1 = 0$, $w_{t+1} = \Pi_W(w_t - \eta_t g(w_t, z_t))$ with $\eta_t = 1/(\lambda t)$ and $z_t \sim D$ i.i.d. In addition, $F$ is $\mu$-smooth with respect to $w^*$, for some $\mu \ge 0$:
--   $$F(w) - F(w^*) \le \frac{\mu}{2}\|w - w^*\|^2 \qquad (w \in W).$$
--
--   **Statement.** For every $T \ge 1$, $F(w_T)$ is integrable and
--   $$\mathbb E\big[F(w_T) - F(w^*)\big] \ \le\ \frac{2\mu G^2}{\lambda^2 T}.$$
--
--   The paper notes that this last-iterate rate is known (Nemirovski et al., 2009) and obtains it as an immediate corollary of Lemma 1 and smoothness. It is the companion of Theorem 2, which gives the same $O(1/T)$ rate for the average of the iterates.
--
--   **Formalization Note** The paper's $w_T$ is `sgdStrongIterates lam W g S (T - 1)` with $S \sim D^T$. The expectation is a Bochner integral, and its integrability is part of the conclusion, so the bound cannot hold by the convention that a non-integrable function integrates to $0$. The paper does not state the sign of $\mu$; $\mu \ge 0$ is assumed (for $\mu < 0$, (2) forces $W = \{w^*\}$ and the bound would be negative).
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 4, Theorem 1

import Definitions.Def_OptimalSGD_Smooth_Model
import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

namespace OptimalSGD.Smooth

/-- **Theorem 1** (arXiv:1109.5647v7, p. 4). Suppose `F` is `λ`-strongly convex and `µ`-smooth
with respect to `w*` over a convex set `W`, and that `E[‖ĝₜ‖²] ≤ G²`. Then with `ηₜ = 1/(λt)`, for
any `T ≥ 1`, `E[F(w_T) − F(w*)] ≤ 2µG²/(λ²T)`; `F(w_T)` is integrable. The paper's `w_T` is
`sgdStrongIterates lam W g S (T - 1)`. -/
theorem theorem_1 {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (G : ℝ) (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {μ : ℝ} (hμ : 0 ≤ μ) (hsmooth : IsSmoothWrt W F μ wstar)
    (T : ℕ) (hT : 1 ≤ T) :
    Integrable (fun S => F (sgdStrongIterates lam W g S (T - 1))) (iidLaw D T) ∧
      (∫ S, F (sgdStrongIterates lam W g S (T - 1)) ∂(iidLaw D T)) - F wstar ≤
        2 * μ * G ^ 2 / (lam ^ 2 * T) := by sorry

end OptimalSGD.Smooth
