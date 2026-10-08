-- Prove2me | Theorems.Thm_OptimalSGD_Smooth_lemma_1
-- name    : OptimalSGD.Smooth.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:45.195395+00:00
-- url     : https://prove2.me/theorems/a15d6015-47d5-4ea5-8937-42f1441de453
-- title:
--   Lemma 1 — $\mathbb E\|w_T - w^*\|^2 \le 4G^2/(\lambda^2 T)$ for SGD with $\eta_t = 1/(\lambda t)$
-- statement:
--   **Setting.** Let $W \subseteq \mathbb R^d$ be closed and convex with $0 \in W$, let $\lambda > 0$, and let $F$ be $\lambda$-strongly convex on $W$ with a minimizer $w^* \in W$ over $W$. Let $g$ be a measurable stochastic subgradient oracle for $F$ relative to $W$ under a probability distribution $D$, whose second moment is bounded uniformly on the domain:
--   $$\mathbb E_{z\sim D}\|g(w,z)\|^2 \le G^2 \qquad \text{for every } w \in W.$$
--   Projected SGD with step sizes $\eta_t = 1/(\lambda t)$ starts at $w_1 = 0$ and, for $t = 1, 2, \dots$, draws $z_t \sim D$ independently and sets
--   $$w_{t+1} = \Pi_W\big(w_t - \eta_t\, g(w_t, z_t)\big),$$
--   where $\Pi_W$ is the Euclidean projection onto $W$.
--
--   **Statement.** For every $T \ge 1$,
--   $$\mathbb E\big[\|w_T - w^*\|^2\big] \ \le\ \frac{4G^2}{\lambda^2 T}.$$
--
--   This is the "key lemma" of §3 of the paper: Theorem 1 follows from it and smoothness, and it is the input to the averaged-iterate bound of Theorem 2. It needs no smoothness of $F$. The statement is the one of version 7 of the preprint, whose acknowledgements credit a correction to Lemma 1.
--
--   **Formalization Note** The space is $\mathbb R^d$ (`UnderstandingML.Vec d`) in place of the paper's Hilbert space. The run is `UnderstandingML.sgdStrongIterates lam W g S`, indexed from $0$, so the paper's $w_T$ is the iterate with index $T-1$; the sample $S = (z_1,\dots,z_T)$ is drawn from $D^T$ (`UnderstandingML.iidLaw D T`), and the last draw is not used by $w_T$. The expectation is a lower Lebesgue integral of $\|w_T - w^*\|^2$, so the bound carries content without an integrability side condition. "Regardless of how the iterates evolve" (p. 3) is the second-moment bound at every $w \in W$; $W$ closed makes the projection exist.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 4, Lemma 1 (proof App. B.2, p. 14)

import Definitions.Def_OptimalSGD_Smooth_Model
import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

namespace OptimalSGD.Smooth

/-- **Lemma 1** (arXiv:1109.5647v7, p. 4; proof App. B.2, p. 14). Suppose `F` is `λ`-strongly
convex over a convex set `W`, and that `E[‖ĝₜ‖²] ≤ G²`. Then with `ηₜ = 1/(λt)`, for any `T ≥ 1`,
`E[‖w_T − w*‖²] ≤ 4G²/(λ²T)`. The paper's `w_T` is `sgdStrongIterates lam W g S (T - 1)` (index
`0` is `w₁ = 0`), and the expectation is over `S ∼ D^T`. -/
theorem lemma_1 {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (G : ℝ) (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    (T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ S, ENNReal.ofReal (‖sgdStrongIterates lam W g S (T - 1) - wstar‖ ^ 2) ∂(iidLaw D T) ≤
      ENNReal.ofReal (4 * G ^ 2 / (lam ^ 2 * T)) := by sorry

end OptimalSGD.Smooth
