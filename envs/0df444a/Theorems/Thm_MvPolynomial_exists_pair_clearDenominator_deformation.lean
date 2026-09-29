-- Prove2me | Theorems.Thm_MvPolynomial_exists_pair_clearDenominator_deformation
-- name    : MvPolynomial.exists_pair_clearDenominator_deformation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/95a8f825-5c47-5a00-9377-055874d8fc88
-- title:
--   Uniform clearing of denominators in a deformation parameter
-- statement:
--   Let $r,b_1,b_2,\omega,c$ be complex numbers with $r,b_1,b_2,\omega$ all non-zero, let $P$ be a polynomial in three variables over $\mathbb{C}$ (indexed by `Fin 3`), let $D_1,D_2$ be one-variable complex polynomials whose values at $0$ are non-zero, and let $e$ be a natural number. The assertion is that there exist two-variable complex polynomials $p,q$ (indexed by `Fin 2`) with the following two properties. First, $q$ is not identically zero in its first variable along any non-zero value of the second: for every $y\neq 0$ there is an $x$ with $q(x,y)\neq 0$. Second, for all complex $x,y,Z$ with $y\neq 0$, if
--   $$Z\cdot D_1\bigl(b_1y^{-1}(rx)\bigr)\,D_1\bigl(b_2y(rx)\bigr)\,D_2\bigl(\omega (rx)^2\bigr)\,\bigl(\omega (rx)^2\bigr)^{e} \;=\; c\,P\bigl(rx,\;b_1y^{-1},\;b_2y\bigr),$$
--   then $Z\cdot q(x,y) = p(x,y)$. Thus a quantity $Z$ defined implicitly by that relation involving negative powers of $y$ is exhibited as a ratio $p/q$ of honest polynomials in $(x,y)$, with a denominator that does not vanish identically on any line $y = \text{const}\neq 0$. Note that $c$ is not required to be non-zero.
--
--   This is a piece of elementary polynomial algebra: it records that the rational expression defining $Z$ in a one-parameter deformation can be written with a single polynomial numerator and denominator, uniformly in the deformation parameter $y$. It is used in the Langlands–Tunnell part of the development, in the construction of a multivariate polynomial governing the deformed local Rankin–Selberg integral and its functional equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_pair_clearDenominator_deformation.lean

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPolynomial.exists_pair_clearDenominator_deformation
    (r b₁ b₂ ω c : ℂ) (hr : r ≠ 0) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hω : ω ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ) (D₁ D₂ : Polynomial ℂ) (e : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0) :
    ∃ p q : MvPolynomial (Fin 2) ℂ,
      (∀ y : ℂ, y ≠ 0 → ∃ x : ℂ, MvPolynomial.eval ![x, y] q ≠ 0) ∧
      ∀ (x y Z : ℂ), y ≠ 0 →
        Z * (D₁.eval (b₁ * y⁻¹ * (r * x)) * D₁.eval (b₂ * y * (r * x)) * D₂.eval (ω * (r * x) ^ 2) *
            (ω * (r * x) ^ 2) ^ e) =
          c * MvPolynomial.eval ![r * x, b₁ * y⁻¹, b₂ * y] P →
        Z * MvPolynomial.eval ![x, y] q = MvPolynomial.eval ![x, y] p := by sorry
