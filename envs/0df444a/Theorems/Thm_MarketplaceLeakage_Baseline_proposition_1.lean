-- Prove2me | Theorems.Thm_MarketplaceLeakage_Baseline_proposition_1
-- name    : MarketplaceLeakage.Baseline.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:42.255514+00:00
-- url     : https://prove2.me/theorems/735d8782-4aae-4e97-9a50-8c65ff714c1f
-- title:
--   Proposition 1, pp. 9–10 — with uniform switching costs the fee is min{μ, v − c}, leakage is positive but partial, and the marketplace's profit increases in μ
-- statement:
--   Consider the baseline leakage game: a marketplace $M$ charges a per-transaction fee $f\le v-c$; a seller with value $v$ and marginal cost $c<v$ sells on $M$ at price $v$ and sets a direct price $p_d\le v$ to maximize $(p_d-c)G(v-p_d)+(v-c-f)(1-G(v-p_d))$; buyers' switching costs to the direct channel are uniform on $[0,\mu]$, $G(s)=s/\mu$ on $[0,\mu]$. The **leakage** is $G(v-p_d)$ and the marketplace earns $f(1-G(v-p_d))$.
--
--   1. For every $\mu>0$ an equilibrium outcome $(f^*,p_d^*)$ exists, and every equilibrium outcome satisfies
--   $$f^*(\mu)=\min\{\mu,\,v-c\},\qquad p_d^*(\mu)=v-\min\Bigl\{\frac\mu2,\,\frac{v-c}2\Bigr\},$$
--   $$\Pi^*(\mu)=\begin{cases}\dfrac\mu2 & \text{if } \mu\le v-c,\\[4pt] (v-c)\Bigl(1-\dfrac{v-c}{2\mu}\Bigr) & \text{if } \mu\ge v-c,\end{cases}$$
--   and there is positive but partial leakage equal to $\frac1\mu\,(v-p_d^*(\mu))$: that is, $G(v-p_d^*)=\frac1\mu(v-p_d^*)$ and $0<G(v-p_d^*)<1$.
--   2. If $0<\mu_1<\mu_2$, then for any equilibrium outcomes at $\mu_1$ and $\mu_2$: the marketplace's fee weakly increases, the seller's direct price weakly decreases, the extent of leakage weakly decreases, and the marketplace's profit strictly increases.
--
--   Higher switching costs make the direct channel less attractive; the marketplace responds by raising its fee, the seller responds by undercutting more, and in the end the marketplace is strictly better off while leakage never rises.
--
--   **Formalization Note.** The statement uses the reduced game of the paper's §4, in which the seller's marketplace price is fixed at $p_m=v$ "given Lemma 1"; Lemma 1 itself is not posed. Equilibrium outcomes are defined by optimality predicates (seller-optimal direct price; no profitable feasible fee deviation), not by the closed forms. "$p_d^*(\mu)$" is the equilibrium direct price $p_d^*(f^*(\mu))$. The comparative statics are stated for every pair of equilibrium outcomes at two values of $\mu$; "increases" for profit is strict and the other three are weak, as worded on the page. The two branches of $\Pi^*$ agree at $\mu=v-c$; Lean writes the first branch for $\mu\le v-c$. The standing assumptions $c<v$ (p. 5) and $\mu>0$ (p. 9) are hypotheses.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89cc00…3c98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), pp. 9–10, Proposition 1, display (6); proof §8.2, p. 34

import Mathlib
import Definitions.Def_MarketplaceLeakage_Baseline_Setting

namespace MarketplaceLeakage.Baseline

/-- Proposition 1, pp. 9–10. Uniform switching costs on `[0, μ]`, `c < v`.
(a) For every `μ > 0` an equilibrium outcome `(f, pd)` of the reduced game exists, and every one
has `f = min {μ, v − c}`, `pd = v − min {μ/2, (v − c)/2}`, marketplace profit `μ/2` if
`μ ≤ v − c` and `(v − c)(1 − (v − c)/(2μ))` otherwise (6), and leakage
`G(v − pd) = (1/μ)(v − pd)` strictly between `0` and `1`.
(b) For `0 < μ₁ < μ₂` and equilibrium outcomes at `μ₁` and at `μ₂`: the fee weakly increases,
the direct price weakly decreases, leakage weakly decreases, and the marketplace's profit
strictly increases. -/
theorem proposition_1 (v c : ℝ) (hvc : c < v) :
    (∀ μ : ℝ, 0 < μ →
      (∃ f pd : ℝ, IsEq v c μ f pd) ∧
      ∀ f pd : ℝ, IsEq v c μ f pd →
        f = min μ (v - c) ∧
        pd = v - min (μ / 2) ((v - c) / 2) ∧
        MProfit v μ f pd =
          (if μ ≤ v - c then μ / 2 else (v - c) * (1 - (v - c) / (2 * μ))) ∧
        leakage v μ pd = 1 / μ * (v - pd) ∧
        0 < leakage v μ pd ∧ leakage v μ pd < 1) ∧
    (∀ μ₁ μ₂ : ℝ, 0 < μ₁ → μ₁ < μ₂ → ∀ f₁ pd₁ f₂ pd₂ : ℝ,
      IsEq v c μ₁ f₁ pd₁ → IsEq v c μ₂ f₂ pd₂ →
        f₁ ≤ f₂ ∧ pd₂ ≤ pd₁ ∧ leakage v μ₂ pd₂ ≤ leakage v μ₁ pd₁ ∧
        MProfit v μ₁ f₁ pd₁ < MProfit v μ₂ f₂ pd₂) := by sorry

end MarketplaceLeakage.Baseline
