-- Prove2me | Theorems.Thm_FracPSG_Abstract_theorem_5_2_iv_rate
-- name    : FracPSG.Abstract.theorem_5_2_iv_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:08:41.408454+00:00
-- url     : https://prove2.me/theorems/f5ef4755-eb65-4b90-bb2c-cab92a64a44c
-- title:
--   Theorem 5.2(iv), first claim — linear rate of the values for KL exponent ≤ 1/2
-- statement:
--   Under the hypotheses of Theorem 5.2, suppose further that $h$ has the KL property at every point of $\Omega$ with one exponent $a\le\tfrac12$, that $\underline\imath\le1$, and that
--   $$\delta:=\inf_{n\in\mathbb N,i\in I}\alpha_{n-i}\beta_n^2>0\quad\text{and}\quad\frac{\varepsilon_n}{\beta_n}=O\Big(\sqrt{h(z_{n-\bar\imath})-h(z_{n+1-\underline\imath})}\Big)\ \text{as } n\to+\infty. \qquad (21)$$
--   Then there are $\gamma_1>0$ and $\rho\in(0,1)$ such that, writing $\bar h=h(\bar z)$ for $\bar z\in\Omega_0$,
--   $$h(z_n)-\bar h\le\gamma_1\rho^n\qquad\text{for all } n\in\mathbb N .$$
--
--   This is the linear (geometric) rate of the objective values of the abstract framework.
--
--   **Formalization Note** $\delta>0$ is encoded by a lower bound $d>0$ on $\alpha_{n-i}\beta_n^2$ over pairs with $n-i\ge0$. The $O(\cdot)$ in (21) is "there is $C$ with $\varepsilon_n/\beta_n\le C\sqrt{\cdots}$ for all large $n$" (both sides are nonnegative); indices are converted with `Int.toNat`, exact for large $n$. $\bar h$ is represented by quantifying over every $\bar z\in\Omega_0$ (nonempty by Lemma 5.1(i), and $h$ is constant on it); the values are finite and enter through `EReal.toReal`.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 15, Theorem 5.2(iv), first claim

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

namespace FracPSG.Abstract

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Theorem 5.2(iv), first claim (Boţ–Dao–Li, arXiv:2003.04124v2, p. 15): under the hypotheses of
Theorem 5.2, if moreover `h` has the KL property at every point of `Ω` with an exponent `a ≤ 1/2`,
`ı̲ ≤ 1`, `δ = inf_{n, i ∈ I} α_{n-i}βₙ² > 0` and `εₙ/βₙ = O(√(h(z_{n-ı̄}) - h(z_{n+1-ı̲})))` (21),
then there are `γ₁ > 0` and `ρ ∈ (0, 1)` with `h(zₙ) - h̄ ≤ γ₁ρⁿ` for all `n`, where
`h̄ = h(z̄)` for `z̄ ∈ Ω₀`. -/
theorem theorem_5_2_iv_rate {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z) (hH4 : H4 α β ε)
    (hbdd : Bornology.IsBounded (Set.range z))
    (hconst : ∀ z₁ ∈ clusterSet z, ∀ z₂ ∈ clusterSet z, h z₁ = h z₂)
    (hKL : ∀ zbar ∈ clusterSet z, HasKLProperty h zbar)
    {a : ℝ} (ha : a ≤ 1 / 2) (hKLexp : ∀ zbar ∈ clusterSet z, HasKLPropertyExp h zbar a)
    (hilo : ilo ≤ 1) {d : ℝ} (hd : DeltaLowerBound α β ilo ihi d)
    (h21 : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      ε n / β n ≤ C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal -
        (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal)) :
    ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ zbar ∈ omega0 h z, ∀ n : ℕ, (h (z n)).toReal - (h zbar).toReal ≤ γ₁ * ρ ^ n := by sorry

end FracPSG.Abstract
