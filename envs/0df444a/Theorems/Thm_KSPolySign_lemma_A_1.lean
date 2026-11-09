-- Prove2me | Theorems.Thm_KSPolySign_lemma_A_1
-- name    : KSPolySign.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:35:10.688203+00:00
-- url     : https://prove2.me/theorems/81453bfc-c522-48cc-aa92-33f060feed65
-- title:
--   Lemma A.1 — Bernstein bounds
-- statement:
--   Let $P$ be a polynomial on the box $\prod_{j=1}^d[a_j,b_j]$ with $a_j<b_j$. Substitute $x_j=a_j+(b_j-a_j)u_j$, write $P(x)=\sum_\nu A_\nu u^\nu$, let $n_j$ bound the degree in $u_j$, and let $B_\mu$ ($0\le\mu_j\le n_j$) be the tensor-product Bernstein coefficients. Then throughout the box
--   $$\min_\mu B_\mu\le P(x)\le\max_\mu B_\mu.$$
--
--   This turns a polynomial inequality on a box into finitely many exact coefficient checks.
--
--   **Formalization Note** The minimum and maximum over the finite grid are written as the existence of grid points $\mu,\mu'$ with $B_\mu\le P(x)\le B_{\mu'}$.
--
--   Differences from the source:
--   - generalization: rational coefficients and rational endpoints a_j < b_j → real coefficients and real endpoints; reason: the rational case is a special case
--   - encoding: min_μ B_μ ≤ P(x) ≤ max_μ B_μ → ∃ grid points μ, μ′ with B_μ ≤ P(x) ≤ B_μ′; reason: equivalent over the finite nonempty grid
--   - encoding: n_j bounds the degree in u_j → every monomial of the substituted polynomial has exponent ≤ n_j in u_j; reason: same condition
-- source:
--   Z. Song, S. Yue, Polynomial Time Algorithms for the Kadison-Singer Problem, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma A.1, p.71 (PDF p.71)

import Mathlib
import Definitions.Def_KSPolySign_bernsteinCoeff
open Matrix
open scoped ComplexOrder

namespace KSPolySign

/-- **Lemma A.1 (Bernstein bounds).** Song–Yue, *Polynomial Time Algorithms for the Kadison-Singer Problem*, arXiv:2609.19794 (held version, sha256 47d4aaa5…), Lemma A.1, p.71 (PDF p.71).

Let `P` be a polynomial on the box `∏_j [a_j, b_j]`, `a_j < b_j`. Substitute `x_j = a_j + (b_j − a_j)u_j`,
write `P(x) = ∑_ν A_ν u^ν`, let `n_j` bound the degree in `u_j`, and let `B_μ` (`0 ≤ μ_j ≤ n_j`) be the
tensor-product Bernstein coefficients. Then `min_μ B_μ ≤ P(x) ≤ max_μ B_μ` throughout the box.

**Formalization Note** Real coefficients and real box endpoints (the paper's are rational). The
degree bound is: every monomial of the substituted polynomial has exponent at most `n_j` in `u_j`.
Over the finite nonempty grid `{μ : μ_j ≤ n_j}`, "min ≤ P(x) ≤ max" is written as the existence of
grid points `μ`, `μ'` with `B_μ ≤ P(x) ≤ B_μ'`. -/
theorem lemma_A_1 (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (a b : Fin d → ℝ) (hab : ∀ j, a j < b j)
    (N : Fin d → ℕ)
    (hN : ∀ ν ∈ (MvPolynomial.bind₁ (fun j => MvPolynomial.C (a j) +
        MvPolynomial.C (b j - a j) * MvPolynomial.X j) P).support, ∀ j, ν j ≤ N j)
    (x : Fin d → ℝ) (hx : ∀ j, a j ≤ x j ∧ x j ≤ b j) :
    (∃ μ : Fin d → ℕ, (∀ j, μ j ≤ N j) ∧ bernsteinCoeff P a b N μ ≤ MvPolynomial.eval x P) ∧
    ∃ μ : Fin d → ℕ, (∀ j, μ j ≤ N j) ∧ MvPolynomial.eval x P ≤ bernsteinCoeff P a b N μ := by sorry

end KSPolySign
