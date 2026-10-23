-- Prove2me | Theorems.Thm_HubSpokePricing_Lagrangian_corollary_4_7
-- name    : HubSpokePricing.Lagrangian.corollary_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:31:49.165168+00:00
-- url     : https://prove2.me/theorems/d8fb5003-f4a1-4fa6-a4cc-68cc0af747f2
-- title:
--   Corollary 4.7, pp. 21–22 — the Lagrangian policy π(δ) loses at most r̄δ/(m−δ) + (r̄+ω̄)e^{−bδ²/(2(m+n))}, hence O(√(ln n/n))
-- statement:
--   Throughout, $N$ is a hub-and-spoke network with one hub (location $0$), $n\ge 1$ spokes and $m$ resources. A request is of type $(i,0)$ (spoke $i$ to hub) with probability $q_{i0}>0$ and of type $(0,i)$ (hub to spoke $i$) with probability $q_{0i}>0$, these probabilities summing to one; $r_{i0},r_{0i}$ are the one-period expected revenue functions of the demand level $d\in[0,1]$, satisfying Assumption 2.1 with constants $\bar r,\bar\omega>0$.
--
--   **(0) The objects exist.** For $0\le\delta<m$, the perturbed dual (11) has an optimal solution $\lambda^*(\delta)\ge0$; for every $\lambda\ge0$ each spoke problem (6) has an optimal solution; and the original system under the resulting Lagrangian policy has a stationary distribution.
--
--   **(1) Explicit bound.** Let $0\le\delta<m$, $\lambda^*(\delta)$ optimal to (11), $\pi(\delta)$ the Lagrangian policy from optimal solutions $p_i$ of (6) at $\lambda^*(\delta)$, and $\mu$ a stationary distribution of the original system under $\pi(\delta)$, with average revenue $V^{\pi(\delta)}$. Under Assumption 4.1 ($\mathbb E[\tilde X_i(\delta)]=\sum_xx\,p_i(x)\le c$ for all $i$, with $c>0$) and $b=1/(1+c)$, for every initial state $x^0\in\mathcal X$,
--   $$V^{\pi(\delta)}\le V^{\mathrm{OPT}}(x^0)\le V^{\mathrm R}\le V^{\pi(\delta)}+\bar r\cdot\frac{\delta}{m-\delta}+(\bar r+\bar\omega)\cdot\exp\Big(-\frac b2\cdot\frac{\delta^2}{m+n}\Big).$$
--
--   **(2) Asymptotic optimality.** Fix $c,\bar r,\bar\omega>0$ and $0<\kappa_1\le\kappa_2$. There are constants $C$ and $N_0$, depending only on $\kappa_1,\kappa_2,c,\bar r,\bar\omega$, such that for every network with these $\bar r,\bar\omega$, with $n\ge N_0$ spokes and $\kappa_1n\le m\le\kappa_2n$ resources, the choice
--   $$\delta=\sqrt{\tfrac1b\,(m+n)\ln n}$$
--   satisfies $\delta<m$ and, whenever Assumption 4.1 holds at this $\delta$ with the constant $c$,
--   $$V^{\mathrm{OPT}}(x^0)-V^{\pi(\delta)}\;\le\;C\sqrt{\frac{\ln n}{n}}\qquad\text{for every }x^0\in\mathcal X.$$
--
--   This is the paper's main guarantee: a policy computed from decoupled spoke problems is asymptotically optimal, with gap $O(\sqrt{\ln n/n})$, when the numbers of resources and locations grow at the same rate.
--
--   **Formalization Note** Part (0) is added so that parts (1)–(2) cannot hold vacuously; the paper asserts each of these objects (the minimum in (11), the maximum in (6), and Corollary B.11). "$m$ and $n$ grow at the same rate" is read as $\kappa_1n\le m\le\kappa_2n$, and the $O(\cdot)$ as an explicit constant $C$ chosen before the network. Assumption 4.1 is assumed only at the $\delta$ in use. $V^{\pi(\delta)}$ is the stationary average revenue (unique by Corollary B.11), and $V^{\mathrm{OPT}}$ uses a `limsup` over history-dependent feasible policies.
-- source:
--   Balseiro, Brown & Chen, Dynamic Pricing of Relocating Resources in Large Networks, SSRN 3313737 (version of May 23, 2020), https://ssrn.com/abstract=3313737, pp. 21–22, Corollary 4.7, Assumption 4.1

import Mathlib
import Definitions.Def_MarkovChain
import Definitions.Def_HubSpokePricing_Lagrangian_Model

namespace HubSpokePricing.Lagrangian

/-- Corollary 4.7 (pp. 21–22). (0) The optima the statement refers to exist: `λ*(δ)` of (11),
optimal solutions of (6), and a stationary distribution of the original system under the
Lagrangian policy. (1) Under Assumption 4.1 (`𝔼[X̃ᵢ(δ)] ≤ c`), with `b = 1/(1 + c)` and
`0 ≤ δ < m`, `V^π(δ) ≤ V^OPT ≤ V^R ≤ V^π(δ) + r̄ δ/(m − δ) + (r̄ + ω̄) exp(−(b/2) δ²/(m + n))`.
(2) With `δ = √((1/b)(m + n) ln n)`, `V^OPT − V^π(δ) = O(√(ln n / n))` when `m` and `n` grow at
the same rate (`κ₁ n ≤ m ≤ κ₂ n`), with `c`, `r̄`, `ω̄` fixed. -/
theorem corollary_4_7 :
    (∀ N : Network, N.Standing → ∀ δ : ℝ, 0 ≤ δ → δ < N.m →
      (∃ lam : ℝ, IsDualOpt N δ lam) ∧
      (∀ lam : ℝ, 0 ≤ lam → ∀ i : Fin N.n, ∃ s : SpokeSol N.m, SpokeOptimal N lam i s) ∧
      (∀ lam : ℝ, 0 ≤ lam → ∀ sol : Fin N.n → SpokeSol N.m,
        (∀ i, SpokeOptimal N lam i (sol i)) →
        ∃ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ)) ∧
    (∀ N : Network, N.Standing → ∀ c : ℝ, 0 < c → ∀ δ : ℝ, 0 ≤ δ → δ < N.m →
      ∀ lam : ℝ, IsDualOpt N δ lam →
      ∀ sol : Fin N.n → SpokeSol N.m, (∀ i, SpokeOptimal N lam i (sol i)) →
      (∀ i, spokeMean (sol i) ≤ c) →
      ∀ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ →
      ∀ x0 : Fin N.n → ℕ, InX N x0 →
        Vpi N sol μ ≤ VOPT N x0 ∧ VOPT N x0 ≤ VRstar N ∧
        VRstar N ≤ Vpi N sol μ + N.rbar * δ / ((N.m : ℝ) - δ) +
          (N.rbar + N.omega) * Real.exp (-((1 / (1 + c)) / 2) * (δ ^ 2 / ((N.m : ℝ) + N.n)))) ∧
    (∀ κ₁ κ₂ c rb om : ℝ, 0 < κ₁ → κ₁ ≤ κ₂ → 0 < c → 0 < rb → 0 < om →
      ∃ C N₀ : ℝ, ∀ N : Network, N.Standing → N.rbar = rb → N.omega = om →
        N₀ ≤ (N.n : ℝ) → κ₁ * N.n ≤ (N.m : ℝ) → (N.m : ℝ) ≤ κ₂ * N.n →
        Real.sqrt ((1 + c) * ((N.m : ℝ) + N.n) * Real.log N.n) < N.m ∧
        ∀ lam : ℝ, IsDualOpt N (Real.sqrt ((1 + c) * ((N.m : ℝ) + N.n) * Real.log N.n)) lam →
        ∀ sol : Fin N.n → SpokeSol N.m, (∀ i, SpokeOptimal N lam i (sol i)) →
        (∀ i, spokeMean (sol i) ≤ c) →
        ∀ μ : OrigState N → ℝ, MarkovChain.IsStationary (origKernel N sol) μ →
        ∀ x0 : Fin N.n → ℕ, InX N x0 →
          VOPT N x0 - Vpi N sol μ ≤ C * Real.sqrt (Real.log N.n / N.n)) := by sorry

end HubSpokePricing.Lagrangian
