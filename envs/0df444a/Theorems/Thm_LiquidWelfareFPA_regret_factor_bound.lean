-- Prove2me | Theorems.Thm_LiquidWelfareFPA_regret_factor_bound
-- name    : LiquidWelfareFPA.regret_factor_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:53.439494+00:00
-- url     : https://prove2.me/theorems/3ff8c861-8e41-4082-9201-84923d3d1ed4
-- title:
--   Appendix A, p.22 — the factor in front of the regret term is $O(1)$
-- statement:
--   For $\gamma\ge1$ let $\lambda=\lambda_1$ if $\gamma<\gamma_0$ and $\lambda=\lambda_2$ if $\gamma\ge\gamma_0$. Then for every $\gamma\ge1$
--
--   1. $\;1+\dfrac1\lambda=\max\Big\{1+\dfrac1\lambda,\ \dfrac{\gamma\lambda}{1-\lambda},\ \dfrac{\gamma}{c(\lambda)\lambda}\Big\}$;
--   2. $\;\max\Big\{\dfrac{\lambda}{1-\lambda},\dfrac1{c(\lambda)\lambda}\Big\}+\dfrac1{\gamma\lambda}\ \le\ \dfrac1\gamma+\dfrac1{\gamma\lambda}+\dfrac1{\gamma\lambda}$;
--
--   and there is a constant $C'\ge0$ such that for every $\gamma\ge1$
--
--   $$\max\Big\{\frac{\lambda}{1-\lambda},\frac1{c(\lambda)\lambda}\Big\}+\frac1{\gamma\lambda}\ \le\ C' .$$
--
--   This bounds the coefficient of the regret term in Theorem 4.2 uniformly in $\gamma$.
--
--   Differences from the source:
--   - reading: = O(1) for λ ∈ {λ₁, λ₂} → ∃ C' ≥ 0 bounding the factor for every γ ≥ 1, with λ = λ₁ for γ < γ₀ and λ = λ₂ for γ ≥ γ₀; reason: the choice of λ made in the proof, switched at Appendix A's exact γ₀; a bound uniform on the theorem's range γ ≥ 1
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, Appendix A, p.22

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam1
import Definitions.Def_LiquidWelfareFPA_lam2
import Definitions.Def_LiquidWelfareFPA_cfun
import Definitions.Def_LiquidWelfareFPA_gamma0

namespace LiquidWelfareFPA

/-- **The factor in front of the regret term is `O(1)`.**
Fikioris & Tardos, arXiv:2210.07502v4, Appendix A, p.22: "Finally, we need to bound the factor
in front of the regret term for λ ∈ {λ1, λ2}, max{λ/(1−λ), 1/(c(λ)λ)} + 1/(γλ). We use the fact
proven above, that for λ ∈ {λ1, λ2}, 1 + 1/λ = max{1 + 1/λ, γλ/(1−λ), γ/(c(λ)λ)} to get that
max{λ/(1−λ), 1/(c(λ)λ)} + 1/(γλ) ≤ 1/γ + 1/(γλ) + 1/(γλ) = O(1)".

Let `λ(γ) = λ₁(γ)` for `γ < γ₀` and `λ(γ) = λ₂(γ)` for `γ ≥ γ₀`. For every `γ ≥ 1`:
1. `1 + 1/λ = max{1 + 1/λ, γλ/(1−λ), γ/(c(λ)λ)}`;
2. `max{λ/(1−λ), 1/(c(λ)λ)} + 1/(γλ) ≤ 1/γ + 1/(γλ) + 1/(γλ)`;
and there is a constant `C' ≥ 0` with `max{λ/(1−λ), 1/(c(λ)λ)} + 1/(γλ) ≤ C'` for all `γ ≥ 1`.

**Formalization Note** The branch switch is at the exact root `γ₀` (`gamma0`), as in Appendix A. -/
theorem regret_factor_bound :
    (∀ γ : ℝ, 1 ≤ γ →
      let lam := if γ < gamma0 then lam1 γ else lam2 γ
      1 + 1 / lam = max (max (1 + 1 / lam) (γ * lam / (1 - lam))) (γ / (cfun lam * lam)) ∧
        max (lam / (1 - lam)) (1 / (cfun lam * lam)) + 1 / (γ * lam)
          ≤ 1 / γ + 1 / (γ * lam) + 1 / (γ * lam)) ∧
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ γ : ℝ, 1 ≤ γ →
      let lam := if γ < gamma0 then lam1 γ else lam2 γ
      max (lam / (1 - lam)) (1 / (cfun lam * lam)) + 1 / (γ * lam) ≤ C' := by sorry

end LiquidWelfareFPA
