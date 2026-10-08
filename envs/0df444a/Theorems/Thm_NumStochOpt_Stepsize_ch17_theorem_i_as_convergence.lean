-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_ch17_theorem_i_as_convergence
-- name    : NumStochOpt.Stepsize.ch17_theorem_i_as_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:23:46.240913+00:00
-- url     : https://prove2.me/theorems/63f9dab0-0032-43d2-bb61-69a6a3334937
-- title:
--   Ch. 17 Theorem (i) — $X_n\to x^*$ a.s. for adapted stepsizes with $\sum\rho_n=\infty$, $\sum\rho_n^2<\infty$
-- statement:
--   Let $S\subseteq\mathbb R^k$ be closed and convex, $(\Xi,P)$ a probability space, and $q:\mathbb R^k\times\Xi\to\mathbb R$ with $q(x,\cdot)$ integrable. The problem (17.1) is to minimize $f(x)=E_P\,q(x,\cdot)=\int q(x,\xi)\,dP(\xi)$ over $x\in S$. Assume $q(\cdot,\xi)$ is $L^1(P)$-differentiable (17.3): there are integrable $\nabla q(x,\cdot)$ with
--   $$
--   \int\big|q(y,\xi)-q(x,\xi)-\langle y-x,\nabla q(x,\xi)\rangle\big|\,dP(\xi)=o(\|y-x\|)\qquad(y\to x),
--   $$
--   so that $f$ is differentiable with $\nabla f(x)=E\,\nabla q(x,\xi)$. Let $x^*$ be the unique minimizer of $f$ on $S$.
--
--   Let $\xi_0,\xi_1,\dots$ be i.i.d. with law $P$ on a probability space $(\Omega,\mu)$, $\mathcal F_n=\sigma(\xi_0,\dots,\xi_{n-1})$, $X_0=x_0$ a fixed point, and
--   $$
--   X_{n+1}=\Pi_S\big(X_n-\rho_nY_n\big),\qquad Y_n=\nabla q(X_n,\xi_n)\qquad(17.4),(17.4a).
--   $$
--   Assume for all $x\in\mathbb R^k$:
--
--   1. $\langle\nabla f(x),x-x^*\rangle\ge a\|x-x^*\|^2$ with $a>0$;
--   2. $\|\nabla f(x)\|^2\le A+B\|x-x^*\|^2$;
--   3. $E\|\nabla q(x,\xi)-\nabla f(x)\|^2\le C$;
--   4. $\rho_n\ge0$ almost surely and $\rho_n$ is $\mathcal F_n$-measurable.
--
--   Then
--   $$
--   \sum_n\rho_n=\infty\ \text{a.s.}\quad\text{and}\quad\sum_n\rho_n^2<\infty\ \text{a.s.}\quad\Longrightarrow\quad X_n\to x^*\ \text{a.s.}
--   $$
--
--   This is the classical almost-sure convergence of the Robbins–Monro-type projection method, here with random stepsizes that may depend on the observations made so far (an adaptive rule). It is the baseline that part (ii) and Chapter 18 relax by dropping $\sum\rho_n^2<\infty$.
--
--   **Formalization Note** The page prints assumption (ii) as $\|\nabla f(x)\|\le A+B\|x-x^*\|^2$; the proof on p. 357 bounds $\rho_n^2\|\nabla f(X_n)\|^2$ by $\rho_n^2(A+B\|X_n-x^*\|^2)$, and with the printed form the theorem is false ($k=1$, $S=\mathbb R$, $\nabla f(x)=x+x|x|$, no noise, $\rho_n=1/(n+1)$, $X_0=10$ diverges), so the squared form is stated. "$\mathrm{Var}(Y_x)\le C$" for a vector is read as $E\|Y_x-EY_x\|^2\le C$, written as a lower Lebesgue integral. The book indexes $\xi_n,X_n,\mathcal F_n$ from $n=1$; here from $n=0$ (the book's $X_n$ is `X (n-1)`). $a>0$ is added: (i) is a strong-monotonicity condition, and the proof uses $a>0$. $\nabla f$ is Mathlib's `gradient f`, which is the true gradient because (17.3) makes $f$ differentiable.
-- source:
--   G. Ch. Pflug, "Stepsize Rules, Stopping Times and their Implementation in Stochastic Quasigradient Algorithms", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 17, p. 356, Theorem (i), with (17.1)–(17.3) pp. 353–354 and (17.4), (17.4a) p. 355

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.Stepsize

/-- **Theorem (i)** of Pflug, Ch. 17 of Ermoliev & Wets (1988), p. 356: almost sure convergence of
the stochastic quasigradient projection method (17.4), (17.4a) with random, adapted stepsizes.

Problem (17.1): minimize `f(x) = E_P q(x, ·)` over a closed convex `S ⊆ ℝᵏ`, where `q(·, ξ)` is
`L¹(P)`-differentiable with `L¹`-derivative `∇q(x, ξ)` (17.3), so that `∇f(x) = E ∇q(x, ξ)`.
The iterates are `X_{n+1} = Π_S(X_n - ρ_n ∇q(X_n, ξ_n))` with `ξ₀, ξ₁, …` i.i.d. with law `P`
(indices shifted by one against the page: the book's `X_n, ξ_n, 𝓕_n` for `n ≥ 1` are `X (n-1)`,
`ξ (n-1)`, `𝓕 (n-1)` here). `x*` is the unique minimizer of `f` on `S`, `𝓕_n = σ(ξ₀, …, ξ_{n-1})`,
and
(i) `⟨∇f(x), x - x*⟩ ≥ a‖x - x*‖²` with `a > 0`,
(ii) `‖∇f(x)‖² ≤ A + B‖x - x*‖²` (the page prints `‖∇f(x)‖` without the square; the proof uses
the squared bound, and with the printed one the theorem is false),
(iii) `E‖∇q(x, ξ) - ∇f(x)‖² ≤ C` (the page's `Var(Y_x) ≤ C`),
(iv) `ρ_n ≥ 0` and `ρ_n` is `𝓕_n`-measurable.
Then `∑ ρ_n = ∞` a.s. and `∑ ρ_n² < ∞` a.s. imply `X_n → x*` a.s. -/
theorem ch17_theorem_i_as_convergence {k : ℕ} {Ξ Ω : Type*} [MeasurableSpace Ξ]
    [MeasurableSpace Ω]
    (P : Measure Ξ) [IsProbabilityMeasure P] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (q : EuclideanSpace ℝ (Fin k) → Ξ → ℝ)
    (G : EuclideanSpace ℝ (Fin k) → Ξ → EuclideanSpace ℝ (Fin k))
    (f : EuclideanSpace ℝ (Fin k) → ℝ) (S : Set (EuclideanSpace ℝ (Fin k)))
    (xstar x₀ : EuclideanSpace ℝ (Fin k)) (a A B C : ℝ)
    (ξ : ℕ → Ω → Ξ) (ρ : ℕ → Ω → ℝ) (X : ℕ → Ω → EuclideanSpace ℝ (Fin k))
    -- the problem (17.1)–(17.3), case (a)
    (hq_int : ∀ x, Integrable (q x) P)
    (hf : ∀ x, f x = ∫ ξ', q x ξ' ∂P)
    (hG_meas : Measurable (Function.uncurry G))
    (hG_int : ∀ x, Integrable (G x) P)
    (hL1diff : ∀ x, (fun y => ∫ ξ', |q y ξ' - q x ξ' - ⟪y - x, G x ξ'⟫_ℝ| ∂P) =o[𝓝 x]
      (fun y => y - x))
    (hS_closed : IsClosed S) (hS_conv : Convex ℝ S)
    (hxstar : xstar ∈ S ∧ ∀ y ∈ S, f xstar ≤ f y)
    (hunique : ∀ y ∈ S, (∀ z ∈ S, f y ≤ f z) → y = xstar)
    -- assumptions (i)–(iv)
    (ha : 0 < a)
    (hi : ∀ x, a * ‖x - xstar‖ ^ 2 ≤ ⟪gradient f x, x - xstar⟫_ℝ)
    (hii : ∀ x, ‖gradient f x‖ ^ 2 ≤ A + B * ‖x - xstar‖ ^ 2)
    (hiii : ∀ x, ∫⁻ ξ', ENNReal.ofReal (‖G x ξ' - ∫ η, G x η ∂P‖ ^ 2) ∂P ≤ ENNReal.ofReal C)
    (hiv_nonneg : ∀ n, ∀ᵐ ω ∂μ, 0 ≤ ρ n ω)
    (hiv_meas : ∀ n, Measurable[noiseSigma ξ n] (ρ n))
    -- the i.i.d. sequence ξ₀, ξ₁, … with distribution P
    (hξ_meas : ∀ n, Measurable (ξ n))
    (hξ_indep : iIndepFun ξ μ)
    (hξ_law : ∀ n, μ.map (ξ n) = P)
    -- the recursion (17.4), (17.4a)
    (hX0 : ∀ ω, X 0 ω = x₀)
    (hrec : ∀ n ω, X (n + 1) ω = NumStochOpt.QuasiFejer.projX S (X n ω - ρ n ω • G (X n ω) (ξ n ω))) :
    (∀ᵐ ω ∂μ, Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n ω) atTop atTop) →
    (∀ᵐ ω ∂μ, Summable (fun n => ρ n ω ^ 2)) →
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 xstar) := by sorry

end NumStochOpt.Stepsize
