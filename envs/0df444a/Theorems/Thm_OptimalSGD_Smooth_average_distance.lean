-- Prove2me | Theorems.Thm_OptimalSGD_Smooth_average_distance
-- name    : OptimalSGD.Smooth.average_distance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:50.02659+00:00
-- url     : https://prove2.me/theorems/f10aa4e8-925e-4dbc-a6b6-0e8ce692256b
-- title:
--   App. B.3 — averaged iterate: $\mathbb E\|\bar w_T - w^*\|^2 \le 32G^2/(\lambda^2 T)$
-- statement:
--   **Setting.** As in Lemma 1: $W \subseteq \mathbb R^d$ closed and convex with $0 \in W$; $F$ $\lambda$-strongly convex on $W$ ($\lambda > 0$) with minimizer $w^* \in W$ over $W$; a measurable stochastic subgradient oracle $g$ relative to $W$ with $\mathbb E_z\|g(w,z)\|^2 \le G^2$ for all $w \in W$; projected SGD $w_1 = 0$, $w_{t+1} = \Pi_W(w_t - \eta_t g(w_t, z_t))$ with $\eta_t = 1/(\lambda t)$ and $z_t \sim D$ i.i.d. Let
--   $$\bar w_T = \frac{1}{T}(w_1 + \dots + w_T)$$
--   be the average of the first $T$ iterates.
--
--   **Statement.** For every $T \ge 1$,
--   $$\mathbb E\big[\|\bar w_T - w^*\|^2\big] \ \le\ \frac{32 G^2}{\lambda^2 T}.$$
--
--   This is the last displayed bound of the proof of Theorem 2 (App. B.3, p. 15), before smoothness is applied; it uses no smoothness of $F$. The paper obtains it by induction on $t$ from a recursion for $\mathbb E\|\bar w_{t+1} - w^*\|^2$ in terms of $\mathbb E\|\bar w_t - w^*\|^2$ and the bound of Lemma 1, with Lemma 2 as the base case. Theorem 2 then follows by applying smoothness at $\bar w_T \in W$.
--
--   **Formalization Note** The paper's $\bar w_T$ is `UnderstandingML.sgdStrongAverage lam W g S` for $S \sim D^T$, the average of the iterates with indices $0,\dots,T-1$. The expectation is a lower Lebesgue integral.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 15, App. B.3 (proof of Theorem 2), display after 'By an induction argument'

import Definitions.Def_OptimalSGD_Smooth_Model
import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

namespace OptimalSGD.Smooth

/-- **App. B.3, p. 15** (proof of Theorem 2): for the average `w̄_T = (w₁ + … + w_T)/T` of SGD with
`ηₜ = 1/(λt)`, for any `T ≥ 1`, `E[‖w̄_T − w*‖²] ≤ 32G²/(λ²T)`. No smoothness is assumed. The
paper's `w̄_T` is `sgdStrongAverage lam W g S` for `S : Fin T → Z`. -/
theorem average_distance {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W) (hclosed : IsClosed W) (hzero : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (G : ℝ) (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    (T : ℕ) (hT : 1 ≤ T) :
    ∫⁻ S : Fin T → Z, ENNReal.ofReal (‖sgdStrongAverage lam W g S - wstar‖ ^ 2) ∂(iidLaw D T) ≤
      ENNReal.ofReal (32 * G ^ 2 / (lam ^ 2 * T)) := by sorry

end OptimalSGD.Smooth
