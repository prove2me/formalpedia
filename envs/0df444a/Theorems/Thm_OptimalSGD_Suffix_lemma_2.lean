-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_lemma_2
-- name    : OptimalSGD.Suffix.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:41.252692+00:00
-- url     : https://prove2.me/theorems/2fb66e70-26a8-4ce4-a199-881eccb858b1
-- title:
--   Lemma 2 — E[‖ĝ‖²] ≤ G² at w forces ‖w − w*‖² ≤ 4G²/λ²
-- statement:
--   Let $W\subseteq\mathbb R^d$ and let $F$ be $\lambda$-strongly convex on $W$ with $\lambda>0$, i.e. for all $x,y\in W$ and $\theta\in[0,1]$,
--   $$F(\theta x+(1-\theta)y)\le\theta F(x)+(1-\theta)F(y)-\tfrac{\lambda}{2}\theta(1-\theta)\|x-y\|^2 .$$
--   Let $g$ be a stochastic subgradient oracle for $F$ relative to $W$ under the law $D$, and let $w^*\in W$ minimize $F$ over $W$. If $w\in W$ is a point at which the oracle satisfies $\mathbb E_{z\sim D}\|g(w,z)\|^2\le G^2$, then
--   $$\|w-w^*\|^2\le\frac{4G^2}{\lambda^2}.$$
--
--   In the paper the lemma is stated for the starting point $w_1=0$, where the expectation over the deterministic $w_1$ is trivial; this is the case $w=0$. It is the base case of the induction proving Lemma 1.
--
--   **Formalization Note** The space is $\mathbb R^d$ (the paper allows a Hilbert space). The second moment is a lower Lebesgue integral, so the hypothesis also asserts its finiteness.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 12, App. B.1, Lemma 2

import Definitions.Def_OptimalSGD_Suffix_Model

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace OptimalSGD.Suffix

/-- **Lemma 2** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, App. B.1, p. 12). If
`E[‖ĝ‖²] ≤ G²` for the oracle at a point `w ∈ W`, then `‖w − w*‖² ≤ 4G²/λ²`, where `F` is
`λ`-strongly convex on the convex set `W` and `w*` minimizes `F` over `W`. The paper states
it for the starting point `w₁ = 0` (deterministic), which is the instance `w = 0`. -/
theorem lemma_2
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (horacle : IsSubgradientOracleOn W F D g)
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {G : ℝ} (w : Vec d) (hw : w ∈ W)
    (hmoment : ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2)) :
    ‖w - wstar‖ ^ 2 ≤ 4 * G ^ 2 / lam ^ 2 := by sorry

end OptimalSGD.Suffix
