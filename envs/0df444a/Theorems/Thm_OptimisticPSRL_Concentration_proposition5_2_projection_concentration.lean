-- Prove2me | Theorems.Thm_OptimisticPSRL_Concentration_proposition5_2_projection_concentration
-- name    : OptimisticPSRL.Concentration.proposition5_2_projection_concentration
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T00:40:32.874416+00:00
-- url     : https://prove2.me/theorems/e858a6c6-253e-4e9f-8337-d951003a2e42
-- title:
--   Proposition 5.2, p. 9 — |(p̂ − p)ᵀh| ≤ 2√(log(n/ρ) Σ_{i<S} γᵢcᵢ²/n) + 3D log(2/ρ)/n with probability 1 − ρ
-- statement:
--   Let $p\in\Delta^S$ and fix $h\in\mathbb R^S$ with $|h_i-h_{i'}|\le D$ for all states $i,i'$. Let $\hat p$ be the average of $n\ge96$ independent multinoulli trials with parameter $p$, i.e. the empirical probability vector of $n$ iid draws from $p$. Then for every $\rho\in(0,1)$, with probability at least $1-\rho$,
--
--   $$
--   \big|(\hat p-p)^Th\big|\le2\sqrt{\log(n/\rho)\sum_{i<S}\frac{\gamma_ic_i^2}{n}}+3D\,\frac{\log(2/\rho)}{n},
--   $$
--
--   where $\gamma_i=\dfrac{p_i(p_{i+1}+\cdots+p_S)}{p_i+\cdots+p_S}$, $c_i=h_i-H_{i+1}$ and $H_{i+1}=\dfrac{1}{\sum_{j=i+1}^Sp_j}\sum_{j=i+1}^Sh_jp_j$.
--
--   The quantity $\sum_{i<S}\gamma_ic_i^2$ equals the variance of $h$ under $p$, so the bound is of Bernstein type: it scales with the spread of $h$ under the true distribution rather than with $D$ alone. In the paper it is the concentration half of the optimism argument (Lemma 5.3), controlling how far the empirical transition vector can be from the true one along the bias vector.
--
--   **Formalization Note** States are `Fin S` in their natural order (0-based); the range $i<S$ is all states but the last. Ratios with a zero denominator are $0$; no positivity of $p$ is assumed. The probability is computed under the $n$-fold product of the categorical law $\sum_ip_i\delta_i$, and "with probability $1-\rho$" is read as "the event has probability at least $1-\rho$". $\log$ is the natural logarithm. The second term is the printed $3D\log(2/\rho)/n$; the paper's proof, through Corollary B.1, yields $3D\log(n/\rho)/n$, which is larger, but the printed statement is still true (classical Bernstein for iid variables gives a smaller bound), and it is posed as printed.
-- source:
--   Agrawal & Jia, Posterior sampling for reinforcement learning: worst-case regret bounds, arXiv:1705.07041v3, p. 9, Proposition 5.2 (restated and proved in App. A.2, p. 21)

import Mathlib
import Definitions.Def_OptimisticPSRL_Concentration_Setting

namespace OptimisticPSRL.Concentration

open MeasureTheory

/-- **Proposition 5.2** (Agrawal–Jia, arXiv:1705.07041v3, p. 9; restated p. 21). Fix
`h ∈ ℝ^S` with `|h_i − h_{i'}| ≤ D` for all `i, i'`, and let `p̂` be the average of `n ≥ 96`
independent multinoulli trials with parameter `p ∈ Δ^S`. For any `ρ ∈ (0, 1)`, with probability
at least `1 − ρ`,
`|(p̂ − p)ᵀh| ≤ 2 √(log(n/ρ) ∑_{i<S} γ_i c_i² / n) + 3D log(2/ρ)/n`. -/
theorem proposition5_2_projection_concentration {S n : ℕ} (p h : Fin S → ℝ) (D ρ : ℝ)
    (hp : IsProbVec p) (hD : ∀ i i', |h i - h i'| ≤ D) (hn : 96 ≤ n) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    ENNReal.ofReal (1 - ρ) ≤
      trialsLaw n p {ω | |∑ i, (phat ω i - p i) * h i| ≤
        2 * Real.sqrt (Real.log (n / ρ) *
            ∑ i ∈ belowLast S, gammaCoef p i * cCoef p h i ^ 2 / n) +
          3 * D * (Real.log (2 / ρ) / n)} := by sorry

end OptimisticPSRL.Concentration
