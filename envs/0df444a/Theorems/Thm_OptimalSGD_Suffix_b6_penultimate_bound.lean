-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_b6_penultimate_bound
-- name    : OptimalSGD.Suffix.b6_penultimate_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:45.810021+00:00
-- url     : https://prove2.me/theorems/e13a1922-fe54-472b-b708-f5e75fc34af6
-- title:
--   App. B.6 — E[F(w̄ᵅ_T) − F(w*)] ≤ 2G²/(αTλ)(1 + Σ1/t) + G²/(2αTλ) Σ1/t
-- statement:
--   Under the standing assumptions of the paper ($W\subseteq\mathbb R^d$ closed and convex with $0\in W$, $F$ $\lambda$-strongly convex on $W$, $g$ a jointly measurable stochastic subgradient oracle for $F$ relative to $W$ with $\mathbb E_z\|g(w,z)\|^2\le G^2$ on $W$, $w^*$ a minimizer of $F$ over $W$), run projected SGD with $\eta_t=1/(\lambda t)$ from $w_1=0$ on an i.i.d. sample $z_1,\dots,z_T\sim D$, $T\ge1$. Let $\alpha\in(0,1)$ be such that $(1-\alpha)T$ is an integer and let $\bar w^\alpha_T$ be the α-suffix average. Then $F(\bar w^\alpha_T)$ has a finite expectation and
--   $$\mathbb E\big[F(\bar w^{\alpha}_T)-F(w^*)\big]\ \le\ \frac{2G^2}{\alpha T\lambda}\left(1+\sum_{t=(1-\alpha)T+1}^{T}\frac1t\right)+\frac{G^2}{2\alpha T\lambda}\sum_{t=(1-\alpha)T+1}^{T}\frac1t .$$
--
--   This is the bound reached in the proof of Theorem 5 once Lemma 1 and $\eta_t=1/(\lambda t)$ are substituted; bounding the harmonic sum by $\log(1/(1-\alpha))$ then gives Theorem 5.
--
--   **Formalization Note** The suffix average is `suffixAverage` with $k=(1-\alpha)T$. The conjunct asserting integrability of $F(\bar w^\alpha_T)$ prevents the Bochner integral from taking Lean's default value $0$.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 18, App. B.6 (proof of Theorem 5), display after "In particular, since we take η_t = 1/λt"

import Definitions.Def_OptimalSGD_Suffix_Model

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace OptimalSGD.Suffix

/-- **App. B.6, bound after substituting `η_t = 1/(λt)`** (Rakhlin, Shamir, Sridharan,
arXiv:1109.5647v7, p. 18). Under the standing assumptions of §2, `α ∈ (0, 1)` and `k = (1 − α)T`,
with `S ∼ D^T` and `H = Σ_{t=k+1}^T 1/t`:
`E[F(w̄ᵅ_T) − F(w*)] ≤ 2G²/(αTλ) · (1 + H) + G²/(2αTλ) · H`.
The first conjunct records that `F(w̄ᵅ_T)` has a finite expectation. -/
theorem b6_penultimate_bound
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
      2 * G ^ 2 / (α * T * lam) * (1 + ∑ t ∈ Finset.Icc (k + 1) T, (1 / (t : ℝ))) +
        G ^ 2 / (2 * α * T * lam) * ∑ t ∈ Finset.Icc (k + 1) T, (1 / (t : ℝ)) := by sorry

end OptimalSGD.Suffix
