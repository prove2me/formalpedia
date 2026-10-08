-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_theorem_5
-- name    : OptimalSGD.Suffix.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:45.925077+00:00
-- url     : https://prove2.me/theorems/30df0d36-3006-4181-bd64-24d8478eb786
-- title:
--   Theorem 5 — SGD with α-suffix averaging: E[F(w̄ᵅ_T) − F(w*)] ≤ (2 + 2.5 log(1/(1−α)))/α · G²/(λT)
-- statement:
--   Let $W\subseteq\mathbb R^d$ be closed and convex with $0\in W$, and let $F:\mathbb R^d\to\mathbb R$ be $\lambda$-strongly convex on $W$ for some $\lambda>0$. Let $D$ be a probability law on a sample space $\mathcal Z$ and $g:\mathbb R^d\times\mathcal Z\to\mathbb R^d$ a jointly measurable stochastic gradient oracle such that, for every $w\in W$, $g(w,z)$ is integrable, its mean $\mathbb E_{z\sim D}\,g(w,z)$ is a subgradient of $F$ at $w$ relative to $W$, and
--   $$\mathbb E_{z\sim D}\|g(w,z)\|^2\le G^2 .$$
--   Let $w^*\in W$ minimize $F$ over $W$. Run projected SGD with step sizes $\eta_t=1/(\lambda t)$ on an i.i.d. sample $z_1,\dots,z_T\sim D$, $T\ge1$:
--   $$w_1=0,\qquad w_{t+1}=\Pi_W\big(w_t-\eta_t\,g(w_t,z_t)\big),$$
--   and let $\alpha\in(0,1)$ be such that $(1-\alpha)T$ is an integer. Return the **α-suffix average**
--   $$\bar w^{\alpha}_T=\frac{w_{(1-\alpha)T+1}+\dots+w_T}{\alpha T}.$$
--   Then $F(\bar w^\alpha_T)$ has a finite expectation and
--   $$\mathbb E\big[F(\bar w^{\alpha}_T)-F(w^*)\big]\ \le\ \frac{2+2.5\log\frac{1}{1-\alpha}}{\alpha}\cdot\frac{G^2}{\lambda T}.$$
--
--   For any fixed $\alpha$ this is an $O(G^2/(\lambda T))$ rate for plain SGD on a non-smooth strongly convex objective, whereas averaging all iterates can lose a $\log T$ factor.
--
--   **Formalization Note** The paper's Hilbert space is specialized to $\mathbb R^d$ (`UnderstandingML.Vec d`). The statement of Theorem 5 on p. 6 writes the hypothesis as $\mathbb E\|\hat g_t\|^2\le G$; the standing assumption of §2 (p. 3) and the proof use $G^2$, which is what is stated here. "Regardless of how the iterates evolve" is rendered as the moment bound at every point of $W$. $\log$ is the natural logarithm. The iterate index in Lean is the paper's $t-1$, and $k=(1-\alpha)T$ is passed as a natural number tied to $\alpha$ by $k=(1-\alpha)T$. Strong convexity is Mathlib's `StrongConvexOn W lam F`, equivalent to the paper's (1) for functions with subgradients relative to $W$ at every point of $W$, which the oracle provides.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 6, Theorem 5 (proof App. B.6, p. 18)

import Definitions.Def_OptimalSGD_Suffix_Model

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace OptimalSGD.Suffix

/-- **Theorem 5** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, §5, p. 6; proof App. B.6,
p. 18). Consider projected SGD started at `w₁ = 0` with step sizes `η_t = 1/(λt)` on the closed
convex set `W ∋ 0`, an i.i.d. sample `S ∼ D^T`, and α-suffix averaging with `α ∈ (0, 1)` and
`k = (1 − α)T` an integer. Suppose `F` is `λ`-strongly convex on `W`, the oracle mean
`E_z g(w, z)` is a subgradient of `F` relative to `W` at every `w ∈ W`, `E‖g(w, z)‖² ≤ G²` at
every `w ∈ W`, and `w*` minimizes `F` over `W`. Then `F(w̄ᵅ_T)` has a finite expectation and
`E[F(w̄ᵅ_T) − F(w*)] ≤ (2 + 2.5 log(1/(1 − α)))/α · G²/(λT)`, `log` the natural logarithm. -/
theorem theorem_5
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (T k : ℕ) (hT : 0 < T) (hk : (k : ℝ) = (1 - α) * T) :
    Integrable (fun S => F (suffixAverage lam W g S k)) (iidLaw D T) ∧
    ∫ S, (F (suffixAverage lam W g S k) - F wstar) ∂(iidLaw D T) ≤
      (2 + 2.5 * Real.log (1 / (1 - α))) / α * (G ^ 2 / (lam * T)) := by sorry

end OptimalSGD.Suffix
