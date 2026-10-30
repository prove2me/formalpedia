-- Prove2me | Theorems.Thm_LyapDiffMC_RandomHorizon_eq_3_8
-- name    : LyapDiffMC.RandomHorizon.eq_3_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:44:38.045666+00:00
-- url     : https://prove2.me/theorems/0ae05755-2233-4cf0-bc11-7e3572d8184b
-- title:
--   (3.8), p. 9 — for f ≥ 0 the random-horizon discounted expectation (3.1) equals Σⱼ (Kʲ(θ)f̃(θ))(x)
-- statement:
--   Throughout, $S$ is a measurable state space, $(P(\theta):\theta\in\Lambda)$ a family of Markov transition kernels on $S$ indexed by an open interval $\Lambda=(a,b)$, $f, g : S\to\mathbb R$ measurable, and $\emptyset\neq C\subseteq S$ measurable. The non-negative kernel $K(\theta,x,dy)=e^{g(x)}P(\theta,x,dy)$ restricted to $y\in C$ is $K(\theta)$, its powers are $K^n(\theta)$ ($K^0(x,dy)=\delta_x(dy)$), $G(\theta,x,dy)=\sum_{n\ge0}K^n(\theta,x,dy)$ (possibly an infinite measure), $\tilde f(\theta,x)=f(x)+\int_{C^c}K(\theta,x,dy)f(y)$, and $u^*(\theta,x)=\sum_{n\ge0}(K^n(\theta)\tilde f(\theta))(x)=\int \tilde f(\theta,y)\,G(\theta,x,dy)$.
--
--   Fix $\theta$ and $x\in C$, and let $\mathbf E^\theta_x$ be the expectation for the chain $X$ with transition kernel $P(\theta)$ started at $X_0=x$. Let $T=\inf\{n\ge0:X_n\in C^c\}$ ($T=\infty$ if $X$ never leaves $C$). If $f\ge0$, then
--   $$\mathbf E^\theta_x\Big[\sum_{j=0}^{T-1}e^{\sum_{k=0}^{j-1}g(X_k)}f(X_j)+e^{\sum_{k=0}^{T-1}g(X_k)}f(X_T)\Big]
--   =\sum_{j=0}^\infty \mathbf E^\theta_x e^{\sum_{k=0}^{j-1}g(X_k)}f(X_j)I(T>j)+\sum_{j=0}^\infty \mathbf E^\theta_x e^{\sum_{k=0}^{j-1}g(X_k)}I(T\ge j)f(X_j)I(X_j\in C^c)
--   =\sum_{j=0}^\infty (K^j(\theta)\tilde f(\theta))(x).$$
--   On $\{T=\infty\}$ the terminal term is absent. All quantities lie in $[0,\infty]$.
--
--   This identifies the path expectation (3.1) with the series $\sum_n K^n(\theta)\tilde f(\theta)$. The rest of the mission uses that series as $u^*$, so this result links the mission's $u^*$ to the chain.
--
--   **Formalization Note** The path law is the published `MarkovChainKernel` (`BanditAlgorithm.markovChainKernel`). The right-hand side is $\int\tilde f(\theta,y)\,G(\theta,x,dy)$ with $\tilde f$ computed in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: E^θ_x, expectation of the chain driven by P(θ) started at x → lintegral against BanditAlgorithm.markovChainKernel (P θ) x; reason: the published path law of the time-homogeneous chain with kernel P(θ) and X₀ = x
--   - encoding: T = inf{n ≥ 0 : Xₙ ∈ Cᶜ}, with T = ∞ when Cᶜ is never hit; the terminal term exp(Σ_{k<T} g)f(X_T) → exitTime in ℕ∞ (⊤ if the path never leaves C); the terminal term is absent on {T = ⊤}; reason: the infinite-horizon reading of p. 3 (C^c = ∅ gives T = ∞ and no terminal reward)
--   - encoding: non-negative real terms and their sums → ENNReal.ofReal of each term, sums and expectations in ℝ≥0∞; reason: every term is non-negative since f ≥ 0; same values in [0, ∞]
--   - encoding: Σⱼ (Kʲ(θ)f̃(θ))(x) → ∫⁻ f̃(θ, y) G(θ, x, dy) with G(θ, x, ·) = Measure.sum of Kʲ(θ, x, ·); reason: the integral against a sum of measures is the sum of the integrals
--   - encoding: θ ∈ Λ with P(θ) a Markov kernel, f, g, C measurability left implicit → any real θ, P θ Markov for every θ ∈ ℝ (Setting), Measurable f, g, MeasurableSet C; reason: the identity holds for every Markov kernel P(θ), so θ ∈ Λ needs no binder; measurability is needed for the expectations and kernel integrals to be defined
-- source:
--   Rhee, Glynn, Lyapunov Conditions for Differentiability of Markov Chain Expectations, arXiv:1707.03870v1, p. 9, (3.8)

import Mathlib
import Definitions.Def_MarkovChainKernel
import Definitions.Def_LyapDiffMC_RandomHorizon_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LyapDiffMC.RandomHorizon

open Classical in
/-- (3.8), p. 9. For non-negative `f`, the random-horizon discounted expectation (3.1) under the
chain with kernel `P(θ)` started at `x ∈ C` splits into the reward collected strictly before the
exit time `T` and the reward collected at time `T` (when `T < ∞`), and this equals
`Σⱼ (Kʲ(θ) f̃(θ))(x) = ∫ f̃(θ, y) G(θ, x, dy)`. -/
theorem eq_3_8 {S : Type*} [MeasurableSpace S] (M : Setting S) (θ : ℝ)
    (hf : ∀ y, 0 ≤ M.f y) (x : S) (hx : x ∈ M.C) :
    ∫⁻ ω, pathReward M ω ∂(BanditAlgorithm.markovChainKernel (M.P θ) x)
        = (∑' j : ℕ, ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          + (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x)) ∧
    (∑' j : ℕ, ∫⁻ ω, (if (j : ℕ∞) < exitTime M ω then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
          + (∑' j : ℕ, ∫⁻ ω,
              (if (j : ℕ∞) ≤ exitTime M ω ∧ ω j ∉ M.C then discReward M ω j else 0)
              ∂(BanditAlgorithm.markovChainKernel (M.P θ) x))
        = ∫⁻ y, ftildeE M θ y ∂(greenMeasure M θ x) := by sorry

end LyapDiffMC.RandomHorizon
