-- Prove2me | Theorems.Thm_MDPFinance_TerminalWealth_binomial_power_utility_monotone
-- name    : MDPFinance.TerminalWealth.binomial_power_utility_monotone
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:54:17.931633+00:00
-- url     : https://prove2.me/theorems/309b05a1-f2f6-4c59-90d2-a2a33d823324
-- title:
--   Lemma 4.2.9 — binomial model: monotonicity of the optimal fraction
-- statement:
--   In the binomial model with power utility ($\gamma<1$, $\gamma\neq0$): a) the optimal fraction
--   $\alpha^*$ is given by (4.9), maximizing the one-period objective on $[\alpha_0,\alpha_1]$;
--   b) $\alpha^*(p)$ is increasing in $p$; c) $\alpha^*((1+i-d)/(u-d)) = 0$ (the zero-mean case).
--
--   **Formalization Note (moderation).** For $\gamma<0$ the one-period problem is the
--   minimization (4.8) on the open interval $(\alpha_0,\alpha_1)$ (Remark 4.2.7), and $\alpha^*$ of
--   (4.9) is its minimizer; for $0<\gamma<1$ it maximizes on $[\alpha_0,\alpha_1]$. Both cases are
--   stated, instead of a maximization claim for every $\gamma \ne 0$, $\gamma<1$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 86, PDF 100, Lemma 4.2.9

import Mathlib
import Definitions.Def_MDPFinance_TerminalWealth_BinomialPower

namespace MDPFinance.TerminalWealth

/-- Lemma 4.2.9 (Bäuerle–Rieder, p. 86, PDF 100). Consider the binomial model with power
utility and parameter `γ < 1`, `γ ≠ 0`, up factor `u`, down factor `down` (`down < 1+i < u`),
up-probability `p ∈ (0,1)`. a) The optimal fraction `α*` invested in the stock is given by (4.9)
(`binomialAlphaStar`): for `0 < γ < 1` it maximizes the one-period objective on `[α_0,α_1]`, and
for `γ < 0` it minimizes it on `(α_0,α_1)` (problem (4.8), Remark 4.2.7). b) `α* = α*(p)` is
increasing in `p`. c) If `p = (1+i-down)/(u-down)` then `α*(p) = 0`. -/
theorem binomial_power_utility_monotone (i u down γ : ℝ) (hγ1 : γ < 1) (hγ0 : γ ≠ 0)
    (hdown : down < 1 + i) (hu : 1 + i < u) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1,
        (0 < γ → IsMaxOn (binomialObjective i u down γ p)
          (Set.Icc (binomialAlpha0 i u) (binomialAlpha1 i down)) (binomialAlphaStar i u down γ p)) ∧
        (γ < 0 → IsMinOn (binomialObjective i u down γ p)
          (Set.Ioo (binomialAlpha0 i u) (binomialAlpha1 i down))
          (binomialAlphaStar i u down γ p))) ∧
      MonotoneOn (binomialAlphaStar i u down γ) (Set.Ioo (0 : ℝ) 1) ∧
      binomialAlphaStar i u down γ ((1 + i - down) / (u - down)) = 0 := by sorry

end MDPFinance.TerminalWealth
