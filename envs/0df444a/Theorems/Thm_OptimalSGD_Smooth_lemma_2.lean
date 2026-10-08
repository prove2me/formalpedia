-- Prove2me | Theorems.Thm_OptimalSGD_Smooth_lemma_2
-- name    : OptimalSGD.Smooth.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:20:47.327919+00:00
-- url     : https://prove2.me/theorems/1a531c1e-8258-45a1-8a54-9768c4bc432d
-- title:
--   Lemma 2 — $\|w - w^*\|^2 \le 4G^2/\lambda^2$ when the oracle's second moment at $w$ is at most $G^2$
-- statement:
--   Let $W \subseteq \mathbb R^d$ be convex, let $\lambda > 0$, and let $F$ be $\lambda$-strongly convex on $W$. Let $g$ be a stochastic subgradient oracle for $F$ relative to $W$ under a probability distribution $D$ (the mean $\mathbb E_z[g(w,z)]$ is a subgradient of $F$ at $w$ relative to $W$), and let $w^* \in W$ minimize $F$ over $W$. If a point $w \in W$ satisfies $\mathbb E_{z \sim D}\|g(w,z)\|^2 \le G^2$, then
--   $$\|w - w^*\|^2 \ \le\ \frac{4G^2}{\lambda^2}.$$
--
--   The paper states this for the deterministic first iterate $w_1$ ("If $\mathbb E[\|\hat g_1\|^2] \le G^2$, then $\mathbb E[\|w_1 - w^*\|^2] \le 4G^2/\lambda^2$"); its proof uses only that $w_1 \in W$, so it is stated here for an arbitrary point of $W$, which contains the paper's case $w = w_1 = 0$. It is the base case of the inductions behind Lemma 1 and the averaged-iterate bound of Theorem 2.
--
--   **Formalization Note** $\lambda$-strong convexity is Mathlib's `StrongConvexOn W lam F` (modulus $\tfrac{\lambda}{2}\|x-y\|^2$), which together with relative subgradients gives the paper's (1). The second moment is a lower Lebesgue integral of $\|g(w,z)\|^2$, so it is meaningful without an integrability assumption.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 12, App. B.1, Lemma 2

import Definitions.Def_OptimalSGD_Smooth_Model
import Definitions.Def_UnderstandingML_Framework

open MeasureTheory UnderstandingML

namespace OptimalSGD.Smooth

/-- **Lemma 2** (arXiv:1109.5647v7, App. B.1, p. 12). If `E[‖ĝ₁‖²] ≤ G²`, then
`E[‖w₁ − w*‖²] ≤ 4G²/λ²`. Stated, as the proof uses it, for an arbitrary point `w ∈ W` in place
of `w₁` (which is deterministic): if `F` is `λ`-strongly convex on the convex set `W`, `g` is a
stochastic subgradient oracle for `F` relative to `W`, `w*` minimizes `F` over `W`, and the
oracle's second moment at `w` is at most `G²`, then `‖w − w*‖² ≤ 4G²/λ²`. -/
theorem lemma_2 {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hW : Convex ℝ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (horacle : OptimalSGD.Suffix.IsSubgradientOracleOn W F D g)
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    (G : ℝ) (w : Vec d) (hw : w ∈ W)
    (hmoment : ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2)) :
    ‖w - wstar‖ ^ 2 ≤ 4 * G ^ 2 / lam ^ 2 := by sorry

end OptimalSGD.Smooth
