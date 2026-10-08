-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_lemma_1
-- name    : OptimalSGD.Suffix.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:40.537177+00:00
-- url     : https://prove2.me/theorems/c8c65d14-15a4-45ab-8afa-1b03d88f0059
-- title:
--   Lemma 1 — E‖w_t − w*‖² ≤ 4G²/(λ²t) for SGD with η_t = 1/(λt)
-- statement:
--   Let $W\subseteq\mathbb R^d$ be closed and convex with $0\in W$, and let $F$ be $\lambda$-strongly convex on $W$ with $\lambda>0$. Let $g$ be a jointly measurable stochastic subgradient oracle for $F$ relative to $W$ under a probability law $D$ (so $\mathbb E_{z\sim D}\, g(w,z)$ is a subgradient of $F$ at $w$ relative to $W$), with
--   $$\mathbb E_{z\sim D}\|g(w,z)\|^2\le G^2\qquad\text{for every } w\in W,$$
--   and let $w^*\in W$ minimize $F$ over $W$. Run projected SGD on an i.i.d. sample $z_1,\dots,z_N\sim D$:
--   $$w_1=0,\qquad w_{t+1}=\Pi_W\Big(w_t-\frac{1}{\lambda t}\,g(w_t,z_t)\Big).$$
--   Then for every $t\ge1$ (with $t\le N+1$, so that $w_t$ is produced by the run),
--   $$\mathbb E\,\|w_t-w^*\|^2\le\frac{4G^2}{\lambda^2 t}.$$
--
--   This is the paper's key lemma: the iterates of SGD with step sizes $1/(\lambda t)$ approach the minimizer at rate $O(1/t)$ in mean square, without any smoothness of $F$. It feeds the analysis of the suffix average.
--
--   **Formalization Note** The space is $\mathbb R^d$ (the paper allows a Hilbert space). The paper states the bound for $w_T$ in a run of length $T$; since $w_t$ only depends on $z_1,\dots,z_{t-1}$, it is stated here for $w_t$ inside a run of any length $N\ge t-1$, which contains the paper's case $N=t$. Lean's iterate index is the paper's $t-1$. The expectation is a lower Lebesgue integral, so the bound also asserts finiteness. This is the version of Lemma 1 in arXiv v7 (whose acknowledgements credit a correction of the lemma).
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 4, Lemma 1 (proof App. B.2, p. 14)

import Definitions.Def_OptimalSGD_Suffix_Model

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace OptimalSGD.Suffix

/-- **Lemma 1** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, p. 4; proof App. B.2, p. 14).
Suppose `F` is `λ`-strongly convex over the closed convex set `W ∋ 0`, the oracle `g` is a
stochastic subgradient oracle for `F` relative to `W` with `E[‖ĝ‖²] ≤ G²` at every point of `W`,
and `w*` minimizes `F` over `W`. Run projected SGD from `w₁ = 0` with `η_t = 1/(λt)` on an
i.i.d. sample `S ∼ D^N`. Then for every `t ≥ 1` (with `t ≤ N + 1`, so that `w_t` is produced
by the run), `E‖w_t − w*‖² ≤ 4G²/(λ²t)`. The paper's `w_t` is `sgdStrongIterates … S (t - 1)`. -/
theorem lemma_1
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    (N t : ℕ) (ht : 1 ≤ t) (htN : t ≤ N + 1) :
    ∫⁻ S, ENNReal.ofReal (‖sgdStrongIterates lam W g S (t - 1) - wstar‖ ^ 2) ∂(iidLaw D N) ≤
      ENNReal.ofReal (4 * G ^ 2 / (lam ^ 2 * t)) := by sorry

end OptimalSGD.Suffix
