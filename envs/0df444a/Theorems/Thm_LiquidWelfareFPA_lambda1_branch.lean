-- Prove2me | Theorems.Thm_LiquidWelfareFPA_lambda1_branch
-- name    : LiquidWelfareFPA.lambda1_branch
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:35.482889+00:00
-- url     : https://prove2.me/theorems/0b5ef46e-3b8d-4304-9b25-405e43cbe3cc
-- title:
--   Appendix A, pp.21–22 — the $\lambda_1$ branch and $\gamma_0$ (corrected: $\gamma<\gamma_0$ for p.9's $\gamma\le1.73$)
-- statement:
--   Let $\lambda_1=1/\sqrt{1+\gamma}$, $c(\lambda)=-1/\ln(1-\lambda)$ and $h(\gamma)=1+\sqrt{\gamma+1}+\gamma\sqrt{\gamma+1}\ln(1-1/\sqrt{\gamma+1})$. Then:
--
--   1. for every $\gamma\ge1$, $\;1+\dfrac1{\lambda_1}=\dfrac{\gamma\lambda_1}{1-\lambda_1}=1+\sqrt{1+\gamma}$;
--   2. for every $\gamma\ge1$, $\;1+\dfrac1{\lambda_1}=\dfrac{\gamma}{c(\lambda_1)\lambda_1}$ if and only if $h(\gamma)=0$;
--   3. $h$ is strictly decreasing on $[1,\infty)$;
--   4. $\gamma_0\ge1$, $h(\gamma_0)=0$, and $\gamma_0$ is the only root of $h$ in $[1,\infty)$;
--   5. $1.725<\gamma_0<1.735$, i.e. $\gamma_0\approx1.73$;
--   6. for every $1\le\gamma<\gamma_0$,
--   $$1+\frac1{\lambda_1}\ >\ \frac{\gamma}{c(\lambda_1)\lambda_1}.$$
--
--   Together these show that for $\gamma<\gamma_0$ the maximum in the aggregated inequality at $\lambda=\lambda_1$ is $1+1/\lambda_1=1+\sqrt{1+\gamma}$.
--
--   Differences from the source:
--   - correction: p.9: 1 + 1/λ₁ ≥ γ/(c(λ₁)λ₁) for γ ≤ 1.73 → 1 + 1/λ₁ > γ/(c(λ₁)λ₁) for 1 ≤ γ < γ₀ (Appendix A's form); reason: γ₀ = 1.72511… < 1.73, and at γ = 1.73 one has 1 + 1/λ₁ ≈ 2.6523 < γ/(c(λ₁)λ₁) ≈ 2.6568
--   - reading: γ₀ ≈ 1.73 → 1.725 < γ₀ < 1.735; reason: two-decimal rounding of 1.72511…
--   - encoding: γ₀ the solution of the equation → γ₀ := inf{γ ≥ 1 : h(γ) ≤ 0}, with h(γ₀) = 0 and uniqueness stated in the item; reason: a closed definition of the root
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, p.9 and Appendix A, pp.21–22

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam1
import Definitions.Def_LiquidWelfareFPA_cfun
import Definitions.Def_LiquidWelfareFPA_hfun
import Definitions.Def_LiquidWelfareFPA_gamma0

namespace LiquidWelfareFPA

/-- **The `λ₁` branch and the threshold `γ₀`.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, p.9 ("we set λ = λ1 = 1/√(1+γ)
(which we get by solving 1 + 1/λ = γλ/(1−λ)) and get 1 + 1/λ1 = γλ1/(1 − λ1) = 1 + √(1+γ) ≥
γ/(c(λ1)λ1)"), and Appendix A, pp.21–22: "let γ0 be the solution to 1 + 1/λ1 = γ/(c(λ1)λ1) ⟺
1 + √(γ+1) = −γ√(γ+1) ln(1 − 1/√(γ+1)). We prove that γ0 is the unique solution by noticing that
1 + √(γ+1) + γ√(γ+1) ln(1 − 1/√(γ+1)) is strictly decreasing for γ ≥ 1 … γ0 ≈ 1.73. These
observations also prove that for γ < γ0, 1 + 1/λ1 > γ/(c(λ1)λ1)".

With `h(γ) = 1 + √(γ+1) + γ√(γ+1) ln(1 − 1/√(γ+1))`:
1. for `γ ≥ 1`, `1 + 1/λ₁ = γλ₁/(1−λ₁) = 1 + √(1+γ)`;
2. for `γ ≥ 1`, `1 + 1/λ₁ = γ/(c(λ₁)λ₁)` if and only if `h(γ) = 0`;
3. `h` is strictly decreasing on `[1, ∞)`;
4. `γ₀ ≥ 1`, `h(γ₀) = 0`, and `γ₀` is the only root of `h` in `[1, ∞)`;
5. `1.725 < γ₀ < 1.735` (that is, `γ₀ ≈ 1.73`);
6. for `1 ≤ γ < γ₀`, `1 + 1/λ₁ > γ/(c(λ₁)λ₁)`.

**Formalization Note** The text's p.9 condition "γ ≤ 1.73" is replaced by Appendix A's
`γ < γ₀` (`γ₀ = 1.72511…`): at `γ = 1.73` one has `1 + 1/λ₁ ≈ 2.6523 < γ/(c(λ₁)λ₁) ≈ 2.6568`. -/
theorem lambda1_branch :
    (∀ γ : ℝ, 1 ≤ γ →
      1 + 1 / lam1 γ = γ * lam1 γ / (1 - lam1 γ) ∧
        γ * lam1 γ / (1 - lam1 γ) = 1 + Real.sqrt (1 + γ)) ∧
    (∀ γ : ℝ, 1 ≤ γ → (1 + 1 / lam1 γ = γ / (cfun (lam1 γ) * lam1 γ) ↔ hfun γ = 0)) ∧
    StrictAntiOn hfun (Set.Ici 1) ∧
    (1 ≤ gamma0 ∧ hfun gamma0 = 0 ∧ ∀ γ : ℝ, 1 ≤ γ → hfun γ = 0 → γ = gamma0) ∧
    (1.725 < gamma0 ∧ gamma0 < 1.735) ∧
    (∀ γ : ℝ, 1 ≤ γ → γ < gamma0 → γ / (cfun (lam1 γ) * lam1 γ) < 1 + 1 / lam1 γ) := by sorry

end LiquidWelfareFPA
