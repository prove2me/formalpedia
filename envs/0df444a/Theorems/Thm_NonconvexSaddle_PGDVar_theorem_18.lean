-- Prove2me | Theorems.Thm_NonconvexSaddle_PGDVar_theorem_18
-- name    : NonconvexSaddle.PGDVar.theorem_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:12:39.314035+00:00
-- url     : https://prove2.me/theorems/cae07994-3e68-4967-903a-d2b2f12d4896
-- title:
--   Theorem 18 — PGD (Variant) makes at least half of its T = Õ(ℓΔ_f/ε²) iterates ε-second-order stationary, w.p. ≥ 1 − δ
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$, $d\ge1$, satisfy Assumption A with constants $\ell,\rho>0$ and be bounded below, with global minimum value $f^\star$. Fix a starting point $x_0$, put $\Delta_f=f(x_0)-f^\star$, and let $\varepsilon,\delta>0$. Let $\iota\ge1$ with $\sqrt{\rho\varepsilon}\le\ell$, and use the parameters of Eq. (6):
--   $$\eta=\frac1\ell,\qquad r=\frac{\varepsilon}{400\iota^3},\qquad \mathscr T=\frac{\ell}{\sqrt{\rho\varepsilon}}\,\iota\in\mathbb N,\qquad \mathscr F=\frac{1}{50\iota^3}\sqrt{\frac{\varepsilon^3}{\rho}} .$$
--   Run Algorithm 4 (Perturbed Gradient Descent, Variant) from $x_0$ with step size $\eta$, perturbation radius $r$, time interval $\mathscr T$ and tolerance $\varepsilon$, with independent perturbations $\xi_0,\dots,\xi_{T-1}\sim\mathrm{Uniform}(B_0(r))$, for
--   $$T=\Bigl\lceil 8\max\Bigl\{\frac{\Delta_f\mathscr T}{\mathscr F},\ \frac{\Delta_f}{\eta\varepsilon^2}\Bigr\}\Bigr\rceil$$
--   iterations, and suppose $\iota$ is large enough that
--   $$\frac{T\ell\sqrt d}{\sqrt{\rho\varepsilon}}\cdot\iota^2 2^{8-\iota}\le\delta .$$
--   Then with probability at least $1-\delta$, at least half of the iterates $x_0,\dots,x_{T-1}$ are $\varepsilon$-second-order stationary points.
--
--   The paper states the iteration count as $\tilde O(\ell\Delta_f/\varepsilon^2)$ with $\iota=c\cdot\log(d\ell\Delta_f/(\rho\varepsilon\delta))$ for an absolute constant $c$. Its proof sets $T=8\max\{\Delta_f\mathscr T/\mathscr F,\Delta_f/(\eta\varepsilon^2)\}=400\iota^4\ell\Delta_f/\varepsilon^2$ and uses about $\iota$ only the displayed condition, which is the hypothesis here. Perturbed gradient descent thus finds approximate second-order stationary points, which excludes strict saddle points, in the number of iterations gradient descent needs for first-order stationarity, up to polylogarithmic factors.
--
--   **Formalization Note** The $t$-th iterate is the point tested at the start of iteration $t$ of Algorithm 4, before a possible perturbation, and "half of its iterations" counts $t\in\{0,\dots,T-1\}$: the statement is $T\le 2\,\#\{t<T: x_t\text{ is an }\varepsilon\text{-SOSP}\}$. The perturbations form a vector in $(\mathbb R^d)^T$ with the product law, and the statement bounds the probability of the failure event by $\delta$. $\mathscr T$ is a natural number equal to $\ell\iota/\sqrt{\rho\varepsilon}$ (no rounding); $\iota\ge1$ and $\ell\ge\sqrt{\rho\varepsilon}$ (footnote 1, p. 14) are the standing assumptions of §5; $2^{8-\iota}$ is a real power; $f^\star$ is the infimum of $f$, finite because $f$ is bounded below. The printed $\iota=c\log(d\ell\Delta_f/(\rho\varepsilon\delta))$ is not invariant under rescaling $x\mapsto\lambda x$ and can be non-positive, so the theorem is stated for every $\iota$ meeting the condition of the proof. The printed proof bounds the number of perturbations by applying Lemma 20 at every perturbation, but Algorithm 4 also perturbs at points that are already $\varepsilon$-second-order stationary, where Lemma 20 does not apply; the statement is posed as printed.
-- source:
--   Jin, Netrapalli, Ge, Kakade, Jordan, On Nonconvex Optimization for Machine Learning: Gradients, Stochasticity, and Saddle Points, arXiv:1902.04811v2, p. 12, Theorem 18 (Algorithm 4 and Eq. (6), p. 12; proof and choice of T and ι, p. 16; footnote 1, p. 14)

import Mathlib
import Definitions.Def_NonconvexSaddle_PGDVar_Setting
import Definitions.Def_NonconvexSaddle_PGDVar_Algorithm4

open scoped RealInnerProductSpace

namespace NonconvexSaddle.PGDVar

open Classical in
/-- Theorem 18, arXiv:1902.04811v2, p. 12, with the parameters of Eq. (6) and the iteration count of
its proof (p. 16). Let `f` satisfy Assumption A and be bounded below, `Δ_f = f(x₀) − f⋆`, `ε, δ > 0`.
Run Algorithm 4 (PGD Variant) from `x₀` with `η = 1/ℓ`, `r = ε/(400ι³)`, `𝒯 = ℓι/√(ρε)` (a natural
number), tolerance `ε`, and i.i.d. perturbations `ξ_0, …, ξ_{T−1} ∼ Uniform(B₀(r))`, for
`T = ⌈8 max{Δ_f𝒯/ℱ, Δ_f/(ηε²)}⌉` iterations, where `ℱ = √(ε³/ρ)/(50ι³)`. If `ι ≥ 1`,
`ℓ ≥ √(ρε)` (footnote 1, p. 14) and `(Tℓ√d/√(ρε))·ι²2^{8−ι} ≤ δ` (the condition the proof imposes on
`ι`), then, except on an event of probability at most `δ`, at least half of the iterates
`x_0, …, x_{T−1}` are `ε`-second-order stationary points. -/
theorem theorem_18 {d : ℕ} (hd : 1 ≤ d) (f : NonconvexSaddle.PSGD.E d → ℝ) (ℓ ρ ε δ ι : ℝ) (hℓ : 0 < ℓ)
    (hρ : 0 < ρ) (hA : NonconvexSaddle.PSGD.AssumptionA f ℓ ρ) (hbdd : BddBelow (Set.range f)) (hε : 0 < ε)
    (hδ : 0 < δ) (hι : 1 ≤ ι) (hfoot : Real.sqrt (ρ * ε) ≤ ℓ)
    (𝒯 : ℕ) (h𝒯 : (𝒯 : ℝ) = timeInterval ℓ ρ ε ι) (x₀ : NonconvexSaddle.PSGD.E d) (T : ℕ)
    (hT : T = ⌈8 * max ((f x₀ - NonconvexSaddle.PSGD.fstar f) * 𝒯 / decr ρ ε ι)
      ((f x₀ - NonconvexSaddle.PSGD.fstar f) / (eta ℓ * ε ^ 2))⌉₊)
    (hιδ : (T * ℓ * Real.sqrt d / Real.sqrt (ρ * ε)) * ι ^ 2 * (2 : ℝ) ^ (8 - ι) ≤ δ) :
    MeasureTheory.Measure.pi (fun _ : Fin T => uniformBall d (radius ε ι))
        {ξ : Fin T → NonconvexSaddle.PSGD.E d | ¬ (T ≤ 2 * ((Finset.range T).filter fun t =>
          IsEpsSOSP f ρ ε (pgdvIter f (eta ℓ) ε 𝒯 x₀ (extendPert ξ) t)).card)} ≤
      ENNReal.ofReal δ := by sorry

end NonconvexSaddle.PGDVar
