-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational
-- name    : LanglandsTunnell.RankinSelberg.rsLocal_fe32_of_mul_eq_middle_of_eq_rational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/f6deca30-048c-5155-ace0-ed1fdbc9408b
-- title:
--   Cleared (3,2) functional equation from a common middle
-- statement:
--   Let $N$ be a natural number with $N>1$, let $Z,D:\mathbb{C}\to\mathbb{C}$ be functions, let $E,Ed$ be complex polynomials, let $\varepsilon,a_1,a_2$ be complex numbers, let $p,q,pd,qd$ be complex polynomials with $q\neq 0$ and $qd\neq 0$, and let $\sigma_2,\sigma_3$ be reals. Assume $Z$ has the cleared rational shape $Z(s)\,q(N^{-s})=p(N^{-s})$ for all $s$ with $\operatorname{Re}s>\sigma_2$, and $D$ has the cleared rational shape $D(s)\,qd(N^{-(1-s)})=pd(N^{-(1-s)})$ for all $s$ with $\operatorname{Re}(1-s)>\sigma_3$. Assume further, with polynomials $m_1,m_2$ ($m_2\neq 0$), an integer $k$ and reals $\sigma_P,\sigma_D$, the two "common middle" identities: $Z(s)\,E(a_1N^{-(s+1/2)})\,E(a_2N^{-(s+1/2)})\,m_2(N^{-s})=m_1(N^{-s})\,N^{ks}$ whenever $\operatorname{Re}s>\sigma_P$, and $D(s)\,Ed(a_1^{-1}N^{-(1/2-s)})\,Ed(a_2^{-1}N^{-(1/2-s)})\,m_2(N^{-s})=\varepsilon^2\,m_1(N^{-s})\,N^{ks}$ whenever $\operatorname{Re}(1-s)>\sigma_D$. The conclusion is the polynomial identity, valid for every $s\in\mathbb{C}$ with no half-plane restriction, $$pd(N^{-(1-s)})\,q(N^{-s})\,Ed(a_1^{-1}N^{-(1/2-s)})\,Ed(a_2^{-1}N^{-(1/2-s)})=p(N^{-s})\,qd(N^{-(1-s)})\,E(a_1N^{-(s+1/2)})\,E(a_2N^{-(s+1/2)})\,\varepsilon^2.$$
--
--   This is the purely algebraic last step in the local $GL_3\times GL_2$ functional equation along the rational-torus route: the two half-planes on which the primal and dual expansions are valid need not overlap, and what links them is the single rational function of $N^{-s}$ exhibited as the common middle by both computations. It is used in the cubic-induction step producing a polynomial witness for the local Rankin–Selberg integrals of deformed spherical data together with their functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsLocal_fe32_of_mul_eq_middle_of_eq_rational.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.RankinSelberg.rsLocal_fe32_of_mul_eq_middle_of_eq_rational
    (N : ℕ) (hN : 1 < N) (Z D : ℂ → ℂ) (E Ed : Polynomial ℂ) (ε a₁ a₂ : ℂ)
    (p q pd qd : Polynomial ℂ) (σ₂ σ₃ : ℝ) (hq : q ≠ 0) (hqd : qd ≠ 0)
    (hZ : ∀ s : ℂ, σ₂ < s.re → Z s * q.eval ((N : ℂ) ^ (-s)) = p.eval ((N : ℂ) ^ (-s)))
    (hD : ∀ s : ℂ, σ₃ < (1 - s).re →
      D s * qd.eval ((N : ℂ) ^ (-(1 - s))) = pd.eval ((N : ℂ) ^ (-(1 - s))))

    (m₁ m₂ : Polynomial ℂ) (k : ℤ) (hm₂ : m₂ ≠ 0)
    (σP σD : ℝ)
    (hP : ∀ s : ℂ, σP < s.re →
      Z s * E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) * E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          m₂.eval ((N : ℂ) ^ (-s)) =
        m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))
    (hDM : ∀ s : ℂ, σD < (1 - s).re →
      D s * Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) * Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          m₂.eval ((N : ℂ) ^ (-s)) =
        ε ^ 2 * (m₁.eval ((N : ℂ) ^ (-s)) * (N : ℂ) ^ ((k : ℂ) * s))) :
    ∀ s : ℂ,
      pd.eval ((N : ℂ) ^ (-(1 - s))) * q.eval ((N : ℂ) ^ (-s)) *
          Ed.eval (a₁⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) *
          Ed.eval (a₂⁻¹ * (N : ℂ) ^ (-(1 / 2 - s))) =
        p.eval ((N : ℂ) ^ (-s)) * qd.eval ((N : ℂ) ^ (-(1 - s))) *
          E.eval (a₁ * (N : ℂ) ^ (-(s + 1 / 2))) *
          E.eval (a₂ * (N : ℂ) ^ (-(s + 1 / 2))) *
          ε ^ 2 := by sorry
