-- Prove2me | Theorems.Thm_OptimalSGD_Suffix_b6_convexity_bound
-- name    : OptimalSGD.Suffix.b6_convexity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:22:44.661828+00:00
-- url     : https://prove2.me/theorems/fc78bd37-0313-4b36-b382-7e3263546368
-- title:
--   App. B.6 — Σ E⟨g_t, w_t − w*⟩ ≥ Σ E[F(w_t) − F(w*)] ≥ αT E[F(w̄ᵅ_T) − F(w*)]
-- statement:
--   Under the standing assumptions of the paper ($W\subseteq\mathbb R^d$ closed and convex with $0\in W$, $F$ $\lambda$-strongly convex on $W$, $g$ a jointly measurable stochastic subgradient oracle for $F$ relative to $W$ with $\mathbb E_z\|g(w,z)\|^2\le G^2$ on $W$, $w^*$ a minimizer of $F$ over $W$), run projected SGD with $\eta_t=1/(\lambda t)$ from $w_1=0$ on an i.i.d. sample $z_1,\dots,z_T\sim D$, $T\ge1$. Let $\alpha\in(0,1)$ be such that $(1-\alpha)T$ is an integer, let $g_t=\mathbb E_{z}\,g(w_t,z)$, and let
--   $$\bar w^{\alpha}_T=\frac{w_{(1-\alpha)T+1}+\dots+w_T}{\alpha T}$$
--   be the α-suffix average. Then $F(w_t)$ ($(1-\alpha)T<t\le T$) and $F(\bar w^\alpha_T)$ have finite expectations, and
--   $$\sum_{t=(1-\alpha)T+1}^{T}\mathbb E\big[\langle g_t,w_t-w^*\rangle\big]\ \ge\ \sum_{t=(1-\alpha)T+1}^{T}\mathbb E\big[F(w_t)-F(w^*)\big]\ \ge\ \alpha T\,\mathbb E\big[F(\bar w^{\alpha}_T)-F(w^*)\big].$$
--
--   The first inequality is the subgradient inequality at each iterate, the second is convexity of $F$ applied to the average; together they turn the summed one-step inequality (3) into a bound on the suffix average.
--
--   **Formalization Note** Lean's iterate index is the paper's $t-1$; the suffix average is `suffixAverage` with $k=(1-\alpha)T$. The two inequalities are stated as a conjunction, after a conjunct asserting the integrability of $F(w_t)$ and $F(\bar w^\alpha_T)$.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 18, App. B.6 (proof of Theorem 5), display after "By convexity of F"

import Definitions.Def_OptimalSGD_Suffix_Model

open MeasureTheory UnderstandingML
open scoped InnerProductSpace

namespace OptimalSGD.Suffix

/-- **App. B.6, convexity display** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, p. 18).
Under the standing assumptions of §2, `η_t = 1/(λt)`, `α ∈ (0, 1)` and `k = (1 − α)T`, with
`S ∼ D^T`:
`Σ_{t=k+1}^T E⟨g_t, w_t − w*⟩ ≥ Σ_{t=k+1}^T E[F(w_t) − F(w*)] ≥ αT · E[F(w̄ᵅ_T) − F(w*)]`,
where `g_t = E_z g(w_t, z)` and `w̄ᵅ_T` is the α-suffix average. The first conjunct records that
the expectations of `F(w_t)` and `F(w̄ᵅ_T)` are finite. -/
theorem b6_convexity_bound
    {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (W : Set (Vec d)) (hWconv : Convex ℝ W) (hWclosed : IsClosed W) (hW0 : (0 : Vec d) ∈ W)
    (F : Vec d → ℝ) {lam : ℝ} (hlam : 0 < lam) (hF : StrongConvexOn W lam F)
    (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracleOn W F D g)
    {G : ℝ} (hmoment : ∀ w ∈ W, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (G ^ 2))
    (wstar : Vec d) (hwstar : wstar ∈ W) (hmin : ∀ w ∈ W, F wstar ≤ F w)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (T k : ℕ) (hT : 0 < T) (hk : (k : ℝ) = (1 - α) * T) :
    ((∀ t ∈ Finset.Icc (k + 1) T,
        Integrable (fun S => F (sgdStrongIterates lam W g S (t - 1))) (iidLaw D T)) ∧
      Integrable (fun S => F (suffixAverage lam W g S k)) (iidLaw D T)) ∧
    ∑ t ∈ Finset.Icc (k + 1) T,
        ∫ S, (F (sgdStrongIterates lam W g S (t - 1)) - F wstar) ∂(iidLaw D T) ≤
      ∑ t ∈ Finset.Icc (k + 1) T,
        ∫ S, ⟪oracleMean D g (sgdStrongIterates lam W g S (t - 1)),
          sgdStrongIterates lam W g S (t - 1) - wstar⟫_ℝ ∂(iidLaw D T) ∧
    α * T * ∫ S, (F (suffixAverage lam W g S k) - F wstar) ∂(iidLaw D T) ≤
      ∑ t ∈ Finset.Icc (k + 1) T,
        ∫ S, (F (sgdStrongIterates lam W g S (t - 1)) - F wstar) ∂(iidLaw D T) := by sorry

end OptimalSGD.Suffix
