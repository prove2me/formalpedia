-- Prove2me | Theorems.Thm_LiuVanRyzin_criticalU_bounds
-- name    : LiuVanRyzin.criticalU_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:38:53.81239+00:00
-- url     : https://prove2.me/theorems/0facadee-6871-4f8b-be3e-48f300e4b3c0
-- title:
--   §3.1 — $U_c$ decreases in $v^0$, $p_1<v^0<p_1+\gamma(p_2-\alpha)$ and $p_1+\gamma(p_2-\alpha)<U_c<p_1+p_2-\alpha$
-- statement:
--   Let $\alpha<p_2<p_1$ and $0<\gamma<1$, and let
--   $$U_c(w)=\frac{(p_2+\gamma(p_1-\alpha))w-p_2(p_1+\gamma(p_2-\alpha))}{w-p_1+\gamma(p_1-p_2)}$$
--   be the expression (8) evaluated at $w$. Then
--
--   1. $U_c(w)$ is strictly decreasing in $w>p_1$;
--   2. if $v^0>p_1$ is the root of the first-order condition (7), then
--   $$v^0<p_1+\gamma(p_2-\alpha)\qquad\text{and}\qquad p_1+\gamma(p_2-\alpha)<U_c(v^0)<p_1+p_2-\alpha.$$
--
--   These bounds give Corollary 1's sufficient conditions for rationing and place $v^0$ inside $[p_1,\bar U]$ whenever $\bar U\ge U_c$.
--
--   **Formalization Note** The paper states the monotonicity of $U_c$ in $v^0$ without a domain; it is stated here on $w>p_1$, where the root lies and the denominator of (8) is positive.
-- source:
--   Liu, van Ryzin, Strategic Capacity Rationing to Induce Early Purchases, Management Science 54(6):1115–1131 (2008), p. 1122, §3.1, bounds on v⁰ and U_c (text preceding Corollary 1)

import Mathlib
import Definitions.Def_LiuVanRyzin_PowerModel

namespace LiuVanRyzin

/-- §3.1, bounds on `v⁰` and `U_c` (Liu–van Ryzin 2008, p. 1122). `U_c` of (8) decreases in
`v⁰`; the root `v⁰` of (7) satisfies `p₁ < v⁰ < p₁ + γ(p₂ - α)`; therefore
`p₁ + γ(p₂ - α) < U_c < p₁ + p₂ - α`. -/
theorem criticalU_bounds (p₁ p₂ α γ : ℝ) (hα : α < p₂) (hp : p₂ < p₁)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    StrictAntiOn (criticalU p₁ p₂ α γ) (Set.Ioi p₁) ∧
      ∀ v₀ : ℝ, p₁ < v₀ → focLHS p₁ p₂ α γ v₀ = 0 →
        v₀ < p₁ + γ * (p₂ - α) ∧
          p₁ + γ * (p₂ - α) < criticalU p₁ p₂ α γ v₀ ∧
          criticalU p₁ p₂ α γ v₀ < p₁ + p₂ - α := by sorry

end LiuVanRyzin
