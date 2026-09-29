-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational
-- name    : LanglandsTunnell.RankinSelberg.forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/4e596acf-715a-59df-84f7-292fe04da066
-- title:
--   Transfer of the local functional equation between rational forms
-- statement:
--   Let $N$ be a natural number with $N>1$, let $Z,D:\mathbb{C}\to\mathbb{C}$ be functions, let $E,E^{\vee}$ (written `E`, `Ed`) be complex polynomials, and let $\varepsilon,a_1,a_2\in\mathbb{C}$. Suppose given a first pair of rational expressions: polynomials $p_0,q_0,p_0^{\vee},q_0^{\vee}$ with $q_0\neq 0$ and $q_0^{\vee}\neq 0$, and reals $\sigma_0,\sigma_0^{\vee}$, such that $Z(s)\,q_0(N^{-s})=p_0(N^{-s})$ whenever $\operatorname{Re} s>\sigma_0$, and $D(s)\,q_0^{\vee}(N^{-(1-s)})=p_0^{\vee}(N^{-(1-s)})$ whenever $\operatorname{Re}(1-s)>\sigma_0^{\vee}$; suppose moreover that for every $s\in\mathbb{C}$ $$p_0^{\vee}(N^{-(1-s)})\,q_0(N^{-s})\,E^{\vee}(a_1^{-1}N^{-(1/2-s)})\,E^{\vee}(a_2^{-1}N^{-(1/2-s)})=p_0(N^{-s})\,q_0^{\vee}(N^{-(1-s)})\,E(a_1N^{-(s+1/2)})\,E(a_2N^{-(s+1/2)})\,\varepsilon^{2}.$$ Suppose given a second pair of rational expressions for the same two functions: polynomials $p,q,p^{\vee},q^{\vee}$ with $q\neq 0$, $q^{\vee}\neq 0$, and reals $\sigma_2,\sigma_3$ with $Z(s)\,q(N^{-s})=p(N^{-s})$ for $\operatorname{Re} s>\sigma_2$ and $D(s)\,q^{\vee}(N^{-(1-s)})=p^{\vee}(N^{-(1-s)})$ for $\operatorname{Re}(1-s)>\sigma_3$. Then the same identity holds for every $s\in\mathbb{C}$ with $p_0,q_0,p_0^{\vee},q_0^{\vee}$ replaced by $p,q,p^{\vee},q^{\vee}$, the polynomials $E,E^{\vee}$, the constants $a_1,a_2$ and the factor $\varepsilon^{2}$ being unchanged.
--
--   This is the bookkeeping step in the local functional equation for Rankin–Selberg convolutions: the $\varepsilon$- and $E$-factors depend only on the functions $Z$ and $D$ and not on the particular rational expression in $N^{-s}$ used to represent them, so a functional equation established for the rational forms coming from one explicit computation holds for any other pair of rational forms on any half-planes. It is used by [`LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge`](thm.html#LanglandsTunnell.CubicInduction.rsLocalIntegral_fe32_of_eq_rational_of_forall_localZeta31_fe_of_gauge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.forall_rsLocal_fe32_of_rsLocal_fe32_of_eq_rational
    (N : ℕ) (hN : 1 < N) (Z D : ℂ → ℂ) (E Ed : Polynomial ℂ) (ε a₁ a₂ : ℂ)

    (p₀ q₀ pd₀ qd₀ : Polynomial ℂ) (σ₀ σd₀ : ℝ) (hq₀ : q₀ ≠ 0) (hqd₀ : qd₀ ≠ 0)
    (hZ₀ : ∀ s : ℂ, σ₀ < s.re → Z s * q₀.eval ((N : ℂ) ^ (-s)) = p₀.eval ((N : ℂ) ^ (-s)))
    (hD₀ : ∀ s : ℂ, σd₀ < (1 - s).re →
      D s * qd₀.eval ((N : ℂ) ^ (-(1 - s))) = pd₀.eval ((N : ℂ) ^ (-(1 - s))))
    (hFE₀ : ∀ s : ℂ,
      pd₀.eval ((N : ℂ) ^ (-(1 - s))) * q₀.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p₀.eval ((N : ℂ) ^ (-s)) * qd₀.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2)

    (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ) (hq : q ≠ 0) (hqd : qd ≠ 0)
    (hZ : ∀ s : ℂ, σ₂ < s.re → Z s * q.eval ((N : ℂ) ^ (-s)) = p.eval ((N : ℂ) ^ (-s)))
    (hD : ∀ s : ℂ, σ₃ < (1 - s).re →
      D s * qd.eval ((N : ℂ) ^ (-(1 - s))) = pd.eval ((N : ℂ) ^ (-(1 - s)))) :
    ∀ s : ℂ,
      pd.eval ((N : ℂ) ^ (-(1 - s))) * q.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p.eval ((N : ℂ) ^ (-s)) * qd.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2 := by sorry
