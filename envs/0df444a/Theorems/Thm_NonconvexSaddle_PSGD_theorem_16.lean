-- Prove2me | Theorems.Thm_NonconvexSaddle_PSGD_theorem_16
-- name    : NonconvexSaddle.PSGD.theorem_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:16:42.336848+00:00
-- url     : https://prove2.me/theorems/e37279d2-f025-44de-95f7-a269589404cf
-- title:
--   Theorem 16 — perturbed SGD makes half its iterates $\epsilon$-second-order stationary within $\tilde O(\ell\Delta_f\mathfrak N/\epsilon^2)$ iterations
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ ($d\ge1$) be bounded below and satisfy Assumption A: it is $\ell$-gradient Lipschitz and $\rho$-Hessian Lipschitz, with $\rho>0$. Let the stochastic gradient $g(x;\theta)$, $\theta\sim\mathcal D$, satisfy Assumption B with level $\sigma>0$ (and optionally Assumption C with constant $\tilde\ell$). Let $\epsilon>0$ with $\sqrt{\rho\epsilon}\le\ell$, let $0<\delta<1$, and let
--   $$\mathfrak N=1+\min\Big\{\frac{\sigma^2}{\epsilon^2}+\frac{\tilde\ell^2}{\ell\sqrt{\rho\epsilon}},\ \frac{\sigma^2d}{\epsilon^2}\Big\}\qquad(\tilde\ell=+\infty\ \text{if Assumption C is not used}).$$
--   Write $\Delta_f=f(x_0)-f^\star$. Run PSGD (Algorithm 2) from $x_0$ with the parameters of Eq. (8),
--   $$\eta=\frac{1}{\iota^9\ell\mathfrak N},\quad r=\iota\epsilon\sqrt{\mathfrak N},\quad \mathscr T=\Big\lceil\frac{\iota}{\eta\sqrt{\rho\epsilon}}\Big\rceil,\quad \mathscr F=\frac1{\iota^5}\sqrt{\frac{\epsilon^3}{\rho}},$$
--   for $T=\lceil100\max\{\Delta_f\mathscr T/\mathscr F,\ \Delta_f/(\eta\epsilon^2)\}\rceil$ iterations. There is an absolute constant $\mu_0>0$ such that, whenever
--   $$\iota\ge\mu_0\,(1+\log Q),\qquad Q=\frac{d\,\mathfrak N\,\max\{1,\ell\Delta_f/\epsilon^2\}\,\ell}{\sqrt{\rho\epsilon}\;\delta},$$
--   with probability at least $1-\delta$ at least half of the iterates $x_0,\dots,x_{T-1}$ are $\epsilon$-second-order stationary points:
--   $$\#\{t<T:\ \|\nabla f(x_t)\|\le\epsilon,\ \nabla^2f(x_t)\succeq-\sqrt{\rho\epsilon}\,I\}\ \ge\ T/2.$$
--
--   Since $\Delta_f\mathscr T/\mathscr F\approx\iota^{15}\ell\mathfrak N\Delta_f/\epsilon^2$, the iteration count is $\tilde O(\ell\Delta_f\mathfrak N/\epsilon^2)$, and whenever $T\ge1$ PSGD visits an $\epsilon$-second-order stationary point. This is the paper's main theorem: with Assumption C and $\sigma^2/\epsilon^2\ge\tilde\ell^2/(\ell\sqrt{\rho\epsilon})$ it matches the $\tilde O(\epsilon^{-4})$ rate of SGD for first-order stationary points, and without it the cost is $\tilde O(d\epsilon^{-4})$.
--
--   **Formalization Note** The paper writes $\tilde O(\cdot)$ and "$(\eta,r)$ chosen as in Eq. (4)"; the proof (App. B.4) uses the explicit parameters of Eq. (8) and the iteration count $T$ above, which is what is stated, with $\mathscr T$ and $T$ rounded up to integers. Its conclusion "at least $T/2$ iterates are $\epsilon$-second-order stationary" is stronger than the printed "visits at least once". The paper calibrates $\iota=\mu\log(d\ell\Delta_f\mathfrak N/(\rho\epsilon\delta))$; that argument is not invariant under rescaling $x\mapsto\lambda x$ and can be $\le0$, so $\iota$ is calibrated by the scale-invariant $Q$, which collects the quantities the proof's failure probabilities $4e^{-\iota}$ and $10d\mathscr T^2T^2\log(\mathscr S\sqrt d/(\eta r))e^{-\iota}$ depend on; $\mu_0$ is an absolute constant quantified before every other object. $\delta<1$ makes the claim non-empty and keeps $\log Q\ge0$; $\sqrt{\rho\epsilon}\le\ell$ is the paper's standing assumption (footnote 1, p. 14). For $\Delta_f=0$, $T=0$ and the statement is empty.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 11, Theorem 16 with Eq. (4); proof App. B.4, pp. 28–29, with Eq. (8), p. 23

import Mathlib
import Definitions.Def_NonconvexSaddle_PSGD_Setting

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace NonconvexSaddle.PSGD

open Classical in
/-- Theorem 16 (arXiv:1902.04811v2, §4.2, p. 11), in the explicit form its proof establishes
(App. B.4, pp. 28–29): with `η, r, 𝒯, ℱ` as in Eq. (8), `ι ≥ μ₀(1 + log Q)` for an absolute constant
`μ₀` and `T = ⌈100 max{Δ_f𝒯/ℱ, Δ_f/(ηε²)}⌉`, with probability at least `1 − δ` at least half of the
iterates `x₀, …, x_{T−1}` of PSGD are `ε`-second-order stationary points. -/
theorem theorem_16 :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ (d : ℕ) (Θ : Type) [MeasurableSpace Θ] (𝒟 : Measure Θ)
      [IsProbabilityMeasure 𝒟] (g : E d → Θ → E d) (f : E d → ℝ) (ℓ ρ σ ε δ N ι : ℝ)
      (x₀ : E d),
      1 ≤ d → AssumptionA f ℓ ρ → AssumptionB f g 𝒟 σ → Measurable (Function.uncurry g) →
      BddBelow (Set.range f) → 0 < ρ → 0 < ε → 0 < δ → δ < 1 → Real.sqrt (ρ * ε) ≤ ℓ →
      IsFrakN g 𝒟 ℓ ρ σ ε N →
      μ₀ * (1 + Real.log (logArgQ d ℓ ρ ε δ N (f x₀ - fstar f))) ≤ ι →
      let η := etaP ι ℓ N
      let r := rP ι ε N
      let 𝒯 := TcalP ι η ρ ε
      let ℱ := FcalP ι ρ ε
      let T := iterT (f x₀ - fstar f) 𝒯 ℱ η ε
      ENNReal.ofReal (1 - δ) ≤
        noiseLaw (d := d) 𝒟 r {ω | (T : ℝ) ≤
          2 * (((Finset.range T).filter
            (fun t => IsEpsSOSP f ρ ε (psgd g η x₀ ω t))).card : ℝ)} := by sorry

end NonconvexSaddle.PSGD
