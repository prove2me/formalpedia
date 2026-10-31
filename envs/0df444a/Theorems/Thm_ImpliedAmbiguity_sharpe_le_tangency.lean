-- Prove2me | Theorems.Thm_ImpliedAmbiguity_sharpe_le_tangency
-- name    : ImpliedAmbiguity.sharpe_le_tangency
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:05:48.75797+00:00
-- url     : https://prove2.me/theorems/9c78b8e9-a6ba-4dc4-b72d-158d2f073fa6
-- title:
--   §4.3 (corrected: positive multiples) — the Sharpe ratio is maximized at the tangency portfolio, $\mathrm{Sr}(\bar x) = (c^\top\Sigma_R^{-1}c)^{1/2}$
-- statement:
--   Let $\Sigma_R$ be a symmetric positive definite $N\times N$ matrix, $\mu\in\mathbb R^N$, $R_f\in\mathbb R$, and suppose the excess return vector $c = \mu - R_f\mathbf 1$ is nonzero. Let $\mathrm{Sr}(x) = c^\top x/(x^\top\Sigma_R x)^{1/2}$ for $x\neq0$ and let $\bar x = \Sigma_R^{-1}c$ be the tangency portfolio. Then
--
--   1. $\mathrm{Sr}$ is homogeneous of degree zero: $\mathrm{Sr}(a x) = \mathrm{Sr}(x)$ for every $a>0$ and $x\neq0$;
--   2. $\mathrm{Sr}$ is maximized at $\bar x$: $\mathrm{Sr}(x)\le\mathrm{Sr}(\bar x)$ for every $x\ne0$, and $\mathrm{Sr}(a\bar x) = \mathrm{Sr}(\bar x)$ for every $a>0$;
--   3. the maximized value is
--   $$
--   \mathrm{Sr}(\bar x) = \bigl(c^\top\Sigma_R^{-1}c\bigr)^{1/2};
--   $$
--   4. the normalized Sharpe ratio $\mathrm{Sr}(x)/\mathrm{Sr}(\bar x)$ lies in $[-1,1]$ for every $x\neq0$.
--
--   These facts make the quantity $\bigl(1-(\mathrm{Sr}(x)/\mathrm{Sr}(\bar x))^2\bigr)^{1/2}$ of Theorem 4 a real number in $[0,1]$.
--
--   Differences from the source:
--   - correction: "maximized at every scalar multiple of the tangency portfolio" → maximized at every positive scalar multiple; reason: false for negative multiples — N = 1, Σ_R = 1, µ − R_f1 = 1 gives Sr(−1) = −1 < 1 = Sr(1).
--   - reading: "homogeneous of degree zero" → Sr(a x) = Sr(x) for a > 0; reason: for a < 0, Sr(a x) = −Sr(x), so only positive homogeneity holds; that is the economic usage.
--   - encoding: Sr : ℝᴺ∖{0} → ℝ evaluated at x̄ → total `sharpe` with `Real.sqrt`, hypotheses x ≠ 0 and µ − R_f1 ≠ 0; reason: x̄ = 0 exactly when µ − R_f1 = 0, so the hypotheses exclude only the inputs outside Sr's domain.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), §4.3, p.21 (paragraph after the definition of Sr)

import Mathlib
import Definitions.Def_ImpliedAmbiguity_excessReturn
import Definitions.Def_ImpliedAmbiguity_sharpe
import Definitions.Def_ImpliedAmbiguity_tangency

open Matrix

namespace ImpliedAmbiguity

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
§4.3, p.21: "The function Sr is homogeneous of degree zero and maximized at every scalar multiple
of the tangency portfolio, say, x̄ ≡ Σ_R⁻¹(µ − R_f1). The maximized value Sr(x̄) is equal to
((µ − R_f1)ᵀΣ_R⁻¹(µ − R_f1))^{1/2}. We thus call the ratio Sr(x)/Sr(x̄) as the normalized Sharpe
ratio of portfolio x, which lies on [−1, 1]."

Corrected statement (for `Σ_R` positive definite and `µ − R_f1 ≠ 0`): (a) `Sr(a x) = Sr(x)` for
`a > 0` and `x ≠ 0`; (b) `Sr(x) ≤ Sr(x̄)` for every `x ≠ 0`, and `Sr(a x̄) = Sr(x̄)` for every
`a > 0`; (c) `Sr(x̄) = ((µ − R_f1)ᵀΣ_R⁻¹(µ − R_f1))^{1/2}`; (d) `Sr(x)/Sr(x̄) ∈ [−1, 1]` for
`x ≠ 0`. The page's "every scalar multiple" is false for negative multiples (`N = 1`,
`Σ_R = 1`, `µ − R_f1 = 1`: `Sr(−1) = −1 < 1 = Sr(1)`), so (b) says "every positive scalar
multiple"; "homogeneous of degree zero" is read as positive homogeneity (for `a < 0` the sign
of `Sr` flips).

**Formalization Note.** `Sr` is `sharpe SigmaR (excessReturn μ Rf)`, total with `Real.sqrt`; the
paper's domain `R^N∖{0}` is enforced by the hypotheses `x ≠ 0` and `µ − R_f1 ≠ 0` (the latter
makes `x̄ ≠ 0`). -/
theorem sharpe_le_tangency {N : ℕ} (SigmaR : Matrix (Fin N) (Fin N) ℝ) (hSigmaR : SigmaR.PosDef)
    (μ : Fin N → ℝ) (Rf : ℝ) (hc : excessReturn μ Rf ≠ 0) :
    let c := excessReturn μ Rf
    let xbar := tangency SigmaR c
    (∀ a : ℝ, 0 < a → ∀ x : Fin N → ℝ, x ≠ 0 → sharpe SigmaR c (a • x) = sharpe SigmaR c x) ∧
    (∀ x : Fin N → ℝ, x ≠ 0 → sharpe SigmaR c x ≤ sharpe SigmaR c xbar) ∧
    (∀ a : ℝ, 0 < a → sharpe SigmaR c (a • xbar) = sharpe SigmaR c xbar) ∧
    sharpe SigmaR c xbar = Real.sqrt (c ⬝ᵥ (SigmaR⁻¹ *ᵥ c)) ∧
    (∀ x : Fin N → ℝ, x ≠ 0 →
      sharpe SigmaR c x / sharpe SigmaR c xbar ∈ Set.Icc (-1 : ℝ) 1) := by sorry

end ImpliedAmbiguity
