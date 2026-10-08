-- Prove2me | Theorems.Thm_FracPSG_Abstract_theorem_5_2
-- name    : FracPSG.Abstract.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:51.853132+00:00
-- url     : https://prove2.me/theorems/960ea52a-4c76-435a-b3aa-ebf1dcb803f1
-- title:
--   Theorem 5.2 — abstract convergence: finite length, convergence, stationarity and linear rates
-- statement:
--   Let $\mathcal H,\mathcal K$ be finite-dimensional real Hilbert spaces, $h:\mathcal K\to(-\infty,+\infty]$ proper and lower semicontinuous, $(x_n)$ in $\mathcal H$ and $(z_n)$ in $\mathcal K$, $\alpha_n,\beta_n>0$, $\Delta_n,\varepsilon_n\ge0$ with $\Delta_k=0$ for $k<0$, integers $\underline\imath\le\bar\imath$, $I=\{\underline\imath,\dots,\bar\imath\}$, and weights $\lambda_i\ge0$ summing to $1$. Suppose that (H1), (H2), (H3), (H4) hold and that $(z_n)$ is bounded. Let $\Omega$ be the set of cluster points of $(z_n)$, suppose that $h$ is constant on $\Omega$ and has the KL property at each point of $\Omega$, let $\Omega_0=\{\bar z\in\Omega:h(z_n)\to h(\bar z)\}$ and $\bar h:=h(\bar z)$ for $\bar z\in\Omega_0$. Then:
--
--   1. $\displaystyle\sum_{n=0}^{+\infty}\Delta_n<+\infty$.
--   2. If (H5) holds, then $\sum_{n=0}^{+\infty}\|x_{n+1}-x_n\|<+\infty$ and $(x_n)$ converges.
--   3. If $\inf_n\beta_n>0$, then $0\in\partial_L h(\bar z)$ for all $\bar z\in\Omega_0$.
--   4. If moreover $h$ has the KL property at every point of $\Omega$ with an exponent $a\le\tfrac12$, $\underline\imath\le1$, $\delta:=\inf_{n,i\in I}\alpha_{n-i}\beta_n^2>0$ and $\varepsilon_n/\beta_n=O\big(\sqrt{h(z_{n-\bar\imath})-h(z_{n+1-\underline\imath})}\big)$ (21), then there are $\gamma_1>0$ and $\rho\in(0,1)$ with
--   $$h(z_n)-\bar h\le\gamma_1\rho^n\quad\text{for all }n;$$
--   and if additionally (H5) holds and $\sum_{k=n}^{+\infty}\varepsilon_k=O\big(\sqrt{h(z_{n-\bar\imath})-\bar h}\big)$, then there are $\bar x\in\mathcal H$ and $\gamma_2>0$ with
--   $$\|x_n-\bar x\|\le\gamma_2\rho^{n/2}\quad\text{for all }n,$$
--   with the same $\rho$.
--
--   The theorem is an abstract convergence result for inexact multi-step descent methods: any algorithm whose iterates satisfy (H1)–(H5) for a KL merit function inherits finite length, global convergence, stationarity of the limit and, under exponent $\le\tfrac12$, linear rates. The paper applies it to the extrapolated proximal subgradient method for fractional programs.
--
--   **Formalization Note** $\mathcal H=$ `EuclideanSpace ℝ (Fin N)`, $\mathcal K=$ `EuclideanSpace ℝ (Fin P)`; $\Delta$ is indexed by $\mathbb Z$. Distances to $\partial_L h$ are encoded by quantifying over subgradients, never with `Metric.infDist`. The infima $\inf\beta_n>0$ and $\delta>0$ are encoded by positive lower bounds ($\delta$ over pairs with $n-i\ge0$, where $\alpha_{n-i}$ is defined). Each $O(\cdot)$ hypothesis is "there is $C$ such that eventually $\cdots\le C\sqrt{\cdots}$". $\bar h$ is $h(\bar z)$ for $\bar z\in\Omega_0$: the value bound is stated for every $\bar z\in\Omega_0$, and the tail-of-errors hypothesis for some $\bar z\in\Omega_0$ (equivalent, since $\Omega_0\ne\emptyset$ and $h$ is constant on it). The KL property is the published `HasKLProperty` with $\eta$ real and without the requirement $\bar z\in\operatorname{dom}\partial_L h$; this makes the hypothesis at most as strong as the paper's.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 15, Theorem 5.2 (i)–(iv)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Theorem 5.2 (Abstract convergence; Boţ–Dao–Li, arXiv:2003.04124v2, p. 15). Under (H1)–(H4), with
`(zₙ)` bounded and `h` constant on the set `Ω` of cluster points and having the KL property at each
point of `Ω`, and `h̄ = h(z̄)` for `z̄ ∈ Ω₀`:
(i) `∑ Δₙ < +∞`;
(ii) under (H5), `∑ ‖xₙ₊₁ - xₙ‖ < +∞` and `(xₙ)` converges;
(iii) if `inf βₙ > 0`, then `0 ∈ ∂_L h(z̄)` for all `z̄ ∈ Ω₀`;
(iv) if moreover `h` has the KL property on `Ω` with an exponent `a ≤ 1/2`, `ı̲ ≤ 1`, `δ > 0` and
(21) holds, there are `γ₁ > 0` and `ρ ∈ (0, 1)` with `h(zₙ) - h̄ ≤ γ₁ρⁿ` for all `n`; and if in
addition (H5) holds and `∑_{k ≥ n} ε_k = O(√(h(z_{n-ı̄}) - h̄))`, there are `x̄` and `γ₂ > 0` with
`‖xₙ - x̄‖ ≤ γ₂ρ^{n/2}` for all `n` (the same `ρ`). -/
theorem theorem_5_2 {N : ℕ} {x : ℕ → EuclideanSpace ℝ (Fin N)} {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z) (hH4 : H4 α β ε)
    (hbdd : Bornology.IsBounded (Set.range z))
    (hconst : ∀ z₁ ∈ clusterSet z, ∀ z₂ ∈ clusterSet z, h z₁ = h z₂)
    (hKL : ∀ zbar ∈ clusterSet z, HasKLProperty h zbar) :
    Summable (fun n : ℕ => Δ n) ∧
    (H5 x Δ → Summable (fun n : ℕ => ‖x (n + 1) - x n‖) ∧
      ∃ xbar : EuclideanSpace ℝ (Fin N), Tendsto x atTop (𝓝 xbar)) ∧
    ((∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ β n) →
      ∀ zbar ∈ omega0 h z, (0 : EuclideanSpace ℝ (Fin P)) ∈ LimitingSubdiff h zbar) ∧
    (∀ a : ℝ, a ≤ 1 / 2 → (∀ zbar ∈ clusterSet z, HasKLPropertyExp h zbar a) →
      ilo ≤ 1 → ∀ d : ℝ, DeltaLowerBound α β ilo ihi d →
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ε n / β n ≤ C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal -
          (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal)) →
      ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        (∀ zbar ∈ omega0 h z, ∀ n : ℕ, (h (z n)).toReal - (h zbar).toReal ≤ γ₁ * ρ ^ n) ∧
        (H5 x Δ →
          (∃ zbar ∈ omega0 h z, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
            ∑' k : ℕ, ε (n + k) ≤
              C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal - (h zbar).toReal)) →
          ∃ xbar : EuclideanSpace ℝ (Fin N), ∃ γ₂ : ℝ, 0 < γ₂ ∧
            ∀ n : ℕ, ‖x n - xbar‖ ≤ γ₂ * ρ ^ ((n : ℝ) / 2))) := by sorry

end FracPSG.Abstract
