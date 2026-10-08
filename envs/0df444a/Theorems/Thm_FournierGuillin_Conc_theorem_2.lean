-- Prove2me | Theorems.Thm_FournierGuillin_Conc_theorem_2
-- name    : FournierGuillin.Conc.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:17.769118+00:00
-- url     : https://prove2.me/theorems/01dd8148-187f-4aff-83d8-123acf70024e
-- title:
--   Theorem 2, p. 3 — ℙ(𝒯_p(μ_N, μ) ≥ x) ≤ a(N, x)1_{x≤1} + b(N, x) under exponential or polynomial moments
-- statement:
--   Let $d\ge1$ and $p>0$, with $p\ge d/2$ or $p\ge1$. Let $\mu\in\mathcal P(\mathbb R^d)$ and let $\mu_N=\frac1N\sum_{k=1}^N\delta_{X_k}$ be the empirical measure of $N$ i.i.d. $\mu$-distributed random variables. Assume one of the conditions
--
--   1. $\mathcal E_{\alpha,\gamma}(\mu)<\infty$ for some $\alpha>p$, $\gamma>0$;
--   2. $\mathcal E_{\alpha,\gamma}(\mu)<\infty$ for some $\alpha\in(0,p)$, $\gamma>0$;
--   3. $M_q(\mu)<\infty$ for some $q>2p$,
--
--   where $M_q(\mu)=\int|x|^q\mu(dx)$ and $\mathcal E_{\alpha,\gamma}(\mu)=\int e^{\gamma|x|^\alpha}\mu(dx)$. Then for all $N\ge1$ and all $x>0$,
--   $$\mathbb P\big(\mathcal T_p(\mu_N,\mu)\ge x\big)\le a(N,x)\mathbf 1_{\{x\le1\}}+b(N,x),$$
--   where
--   $$a(N,x)=C\times\begin{cases}\exp(-cNx^2)&p>d/2,\\ \exp\big(-cN(x/\log(2+1/x))^2\big)&p=d/2,\\ \exp(-cNx^{d/p})&p\in[1,d/2),\end{cases}$$
--   $$b(N,x)=C\times\begin{cases}\exp(-cNx^{\alpha/p})\mathbf 1_{\{x>1\}}&\text{under (1)},\\ \exp(-c(Nx)^{(\alpha-\varepsilon)/p})\mathbf 1_{\{x\le1\}}+\exp(-c(Nx)^{\alpha/p})\mathbf 1_{\{x>1\}}&\forall\varepsilon\in(0,\alpha)\ \text{under (2)},\\ N(Nx)^{-(q-\varepsilon)/p}&\forall\varepsilon\in(0,q)\ \text{under (3)}.\end{cases}$$
--   The positive constants $C$ and $c$ depend only on $p$, $d$ and on $\alpha,\gamma,\mathcal E_{\alpha,\gamma}(\mu)$ (under (1)), on $\alpha,\gamma,\mathcal E_{\alpha,\gamma}(\mu),\varepsilon$ (under (2)), or on $q,M_q(\mu),\varepsilon$ (under (3)).
--
--   This is a non-asymptotic deviation inequality for the transport cost between a measure and its empirical measure, with the rate $a$ (the typical fluctuation, which depends on the dimension) and the tail $b$ (governed by the moments of $\mu$).
--
--   **Formalization Note** The statement is the conjunction of three parts, one per condition, each with its own constants. In each part the parameters ($\alpha,\gamma$ or $q$), the moment value $E_0=\mathcal E_{\alpha,\gamma}(\mu)<\infty$ (resp. $M_0=M_q(\mu)<\infty$) and $\varepsilon$ are quantified before $\exists\,C,c>0$, and $\mu$ (constrained by $\mathcal E_{\alpha,\gamma}(\mu)=E_0$, resp. $M_q(\mu)=M_0$), $N$, $x$ after, which encodes the stated dependence of the constants. The sample $(X_1,\dots,X_N)$ is $\omega$ under the product measure $\mu^{\otimes N}$ on $(\mathbb R^d)^N$; the page's i.i.d. sequence enters only through its first $N$ terms. The probability is $\mu^{\otimes N}$ applied to $\{\omega:\ x\le\mathcal T_p(\mu_N,\mu)\}$ (measurable in fact, so this is the page's quantity), and $\mathcal T_p$ is valued in $[0,\infty]$. **Departures from the print:** the page writes $\mathcal T_p(\mu^N,\mu)$, which is $\mathcal T_p(\mu_N,\mu)$ (its notation of p. 1, and the proof on p. 19). The page opens with "let $p>0$" but prints $a(N,x)$ only for $p>d/2$, $p=d/2$ and $p\in[1,d/2)$; the theorem is posed on that range, $p\ge d/2$ or $p\ge1$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Theorem 2, p. 3; proof §§4–6, assembled pp. 19–20

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Conc_Setting
open MeasureTheory WassersteinDRO.Duality
open scoped ENNReal NNReal

namespace FournierGuillin.Conc

/-- Theorem 2 (Fournier–Guillin, arXiv:1312.2128v1, p. 3): for `μ ∈ P(ℝ^d)` and `p > 0` (posed for
`p ≥ d/2` or `p ≥ 1`, where `a(N, x)` is printed), under each of
(1) `ℰ_{α,γ}(μ) < ∞` for some `α > p`, `γ > 0`;
(2) `ℰ_{α,γ}(μ) < ∞` for some `α ∈ (0, p)`, `γ > 0`;
(3) `M_q(μ) < ∞` for some `q > 2p`,
there are `C, c > 0` depending only on `p, d` and on `α, γ, ℰ_{α,γ}(μ)` (under (1)), on
`α, γ, ℰ_{α,γ}(μ), ε` (under (2)) or on `q, M_q(μ), ε` (under (3)) such that for all `N ≥ 1` and
`x > 0`, `ℙ(𝒯_p(μ_N, μ) ≥ x) ≤ a(N, x) 1_{x ≤ 1} + b(N, x)`. -/
theorem theorem_2 (d : ℕ) (hd : 1 ≤ d) (p : ℝ) (hp : 0 < p)
    (hrange : (d : ℝ) / 2 ≤ p ∨ 1 ≤ p) :
    (∀ α γ : ℝ, p < α → 0 < γ → ∀ E₀ : ℝ≥0∞, E₀ < ⊤ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], expMoment α γ μ = E₀ →
          ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
            Measure.pi (fun _ : Fin N => μ)
                {ω | ENNReal.ofReal x ≤ FournierGuillin.Moment.transportCost p (empiricalDistribution ω) μ} ≤
              ENNReal.ofReal (C * rateA d p c N x * (if x ≤ 1 then 1 else 0) +
                C * Real.exp (-(c * N * x ^ (α / p))) * (if 1 < x then 1 else 0))) ∧
    (∀ α γ : ℝ, 0 < α → α < p → 0 < γ → ∀ E₀ : ℝ≥0∞, E₀ < ⊤ → ∀ ε : ℝ, 0 < ε → ε < α →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], expMoment α γ μ = E₀ →
          ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
            Measure.pi (fun _ : Fin N => μ)
                {ω | ENNReal.ofReal x ≤ FournierGuillin.Moment.transportCost p (empiricalDistribution ω) μ} ≤
              ENNReal.ofReal (C * rateA d p c N x * (if x ≤ 1 then 1 else 0) +
                C * (Real.exp (-(c * (N * x) ^ ((α - ε) / p))) * (if x ≤ 1 then 1 else 0) +
                  Real.exp (-(c * (N * x) ^ (α / p))) * (if 1 < x then 1 else 0)))) ∧
    (∀ q : ℝ, 2 * p < q → ∀ M₀ : ℝ≥0∞, M₀ < ⊤ → ∀ ε : ℝ, 0 < ε → ε < q →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ], FournierGuillin.Moment.moment q μ = M₀ →
          ∀ N : ℕ, 1 ≤ N → ∀ x : ℝ, 0 < x →
            Measure.pi (fun _ : Fin N => μ)
                {ω | ENNReal.ofReal x ≤ FournierGuillin.Moment.transportCost p (empiricalDistribution ω) μ} ≤
              ENNReal.ofReal (C * rateA d p c N x * (if x ≤ 1 then 1 else 0) +
                C * (N * (N * x) ^ (-((q - ε) / p))))) := by sorry

end FournierGuillin.Conc
