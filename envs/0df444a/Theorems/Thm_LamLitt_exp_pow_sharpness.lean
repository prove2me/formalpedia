-- Prove2me | Theorems.Thm_LamLitt_exp_pow_sharpness
-- name    : LamLitt.exp_pow_sharpness
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:25:44.288743+00:00
-- url     : https://prove2.me/theorems/25644583-0285-49d4-b0d3-add48c52877f
-- title:
--   Sharpness of condition (3): the first $mp$ coefficients of $e^{z^m}$ are $p$-integral
-- statement:
--   Let $m\ge 1$ be an integer and let
--
--   $$f(z)=e^{z^m}=\sum_{j\ge 0}\frac{z^{mj}}{j!}\in\mathbb{Q}[[z]],$$
--
--   the power series whose coefficient $a_k$ of $z^k$ is $1/(k/m)!$ if $m$ divides $k$ and $0$ otherwise. Then:
--
--   1. $f$ solves the linear differential equation $f'(z)=m\,z^{m-1}f(z)$. This is an equation $f'=g(z,f)$ with $g(z,y_0)=m\,z^{m-1}y_0$ a polynomial, so it has no singular points.
--   2. For every prime $p$, the first $mp$ Taylor coefficients $a_0,a_1,\dots,a_{mp-1}$ of $f$ have denominators prime to $p$.
--   3. There is no $N$ such that $a_k\in\mathbb{Z}[1/N]$ for all $k$.
--   4. $f$ is not algebraic over $\mathbb{Q}[z]$.
--
--   This is the example of Lam and Litt showing that the growth condition in condition (3) of their conjecture is sharp. Item 2 says that the coefficients of $f$ are $\omega$-integral for $\omega(p)=mp-1$, a function with $\omega(p)/p\to m$. Since $m$ is arbitrary, the requirement $\omega(p)/p\to\infty$ cannot be replaced by a lower bound $\omega(p)\ge mp-1$ for any fixed $m$: such a condition implies neither algebraicity (item 4) nor bounded denominators (item 3).
--
--   **Formalization Note** The series is specified by its coefficients; the quotient $k/m$ is the natural-number quotient and is only used when $m\mid k$. The differential equation is expressed with the mission's predicate `IsSolutionOfAlgebraicODE` for order $1$ and the rational function $g=m\,x_0^{m-1}x_1$, where $x_0$ stands for $z$ and $x_1$ for $f$. Item 2 is stated as: for every prime $p$ and every $k<mp$, the reduced denominator of $a_k$ is coprime to $p$.
-- source:
--   Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175 (v1), Remark 1.1.5, p. 4: 'Condition (3) of Conjecture 1.1.1 is sharp in the sense that, for any integer m > 0, there exist non-algebraic functions satisfying a (linear) algebraic differential equation whose first mp Taylor coefficients have denominators prime to p, for all p. For example, this holds true for the functions e^{z^m} = sum_n z^{nm}/n!.' Formalizing this remark is listed as a TODO in Formal Conjectures, FormalConjectures/LittProblems/1.lean, https://github.com/google-deepmind/formal-conjectures .

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem exp_pow_sharpness (m : ℕ) (hm : 0 < m) (f : PowerSeries ℚ)
    (hf : ∀ k : ℕ, PowerSeries.coeff k f = if m ∣ k then ((k / m).factorial : ℚ)⁻¹ else 0) :
    IsSolutionOfAlgebraicODE 1 f
        (algebraMap (MvPolynomial (Fin (1 + 1)) ℚ) (MvRatFunc (Fin (1 + 1)) ℚ)
          (MvPolynomial.C (m : ℚ) * MvPolynomial.X 0 ^ (m - 1) * MvPolynomial.X 1)) ∧
      (∀ p : Nat.Primes, ∀ k : ℕ, k < m * (p : ℕ) → Nat.Coprime (PowerSeries.coeff k f).den p) ∧
      (¬ ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N) ∧
      ¬ IsAlgebraic (Polynomial ℚ) f := by sorry

end LamLitt
