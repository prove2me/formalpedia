-- Prove2me | Theorems.Thm_NatureSLT_Kernels_christoffel_darboux
-- name    : NatureSLT.Kernels.christoffel_darboux
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:12.246+00:00
-- url     : https://prove2.me/theorems/b194c433-8558-4312-bc5b-db0bb864976a
-- title:
--   Eq. (6.21) — the Christoffel–Darboux formula for the kernel of the first $n$ orthonormal polynomials
-- statement:
--   Let $\mu$ be a measure on the real line under which every power $x^m$, $m \ge 0$, is integrable, and let $P_1, P_2, \dots$ be real polynomials with $\deg P_k = k - 1$ that are orthonormal with respect to $\mu$ up to index $n + 1$:
--
--   $$\int P_i(x) P_j(x)\, d\mu(x) = \delta_{ij}, \qquad 1 \le i, j \le n + 1 .$$
--
--   (Chebyshev, Legendre and Hermite polynomials are examples.) Then there is a constant $a_n$, depending on the family and on $n$, such that the kernel of the first $n$ elements of the basis satisfies
--
--   $$K_n(x, y) = \sum_{k=1}^{n} P_k(x) P_k(y) = a_n\, \frac{P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y)}{x - y} \qquad (x \ne y),$$
--
--   $$K_n(x, x) = \sum_{k=1}^{n} P_k^2(x) = a_n \bigl[P'_{n+1}(x) P_n(x) - P'_n(x) P_{n+1}(x)\bigr] \qquad \text{for all } x.$$
--
--   The formula turns the $n$-term kernel generating expansions on orthonormal polynomials into a closed form involving only two consecutive polynomials.
--
--   **Formalization Note** The book says "the number $n$ of elements in the orthonormal basis" and indexes the basis from $k = 1$, so $P_k$ has degree $k - 1$ (with $\deg P_k = k$ and the sum starting at $k = 1$ the identity would be false). Orthonormality is required for $P_1, \dots, P_{n+1}$, since $P_{n+1}$ appears in the formula. The finiteness of all moments of $\mu$ is the standing setting of orthogonal polynomials (it makes every integral above a genuine one); it holds for all of the book's examples. The first identity is stated for $x \ne y$, where the quotient is defined.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 192, Eq. (6.21)

import Mathlib

open MeasureTheory

namespace NatureSLT.Kernels

/-- Eq. (6.21) (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.3.1, p. 192),
the Christoffel–Darboux formula. `P₁, P₂, …` are orthonormal polynomials with respect to a
measure `μ` on `ℝ` with finite moments of every order; `P_k` has degree `k - 1` (the basis
`P₁, …, P_n` has `n` elements, the first being the constant), and orthonormality is required
for `P₁, …, P_{n+1}`. Then there is a constant `a_n` (depending on the family and on `n`) with
`K_n(x, y) = Σ_{k=1}^n P_k(x) P_k(y) = a_n (P_{n+1}(x) P_n(y) - P_n(x) P_{n+1}(y)) / (x - y)`
for `x ≠ y`, and
`K_n(x, x) = Σ_{k=1}^n P_k(x)² = a_n [P'_{n+1}(x) P_n(x) - P'_n(x) P_{n+1}(x)]`. -/
theorem christoffel_darboux (μ : Measure ℝ) (hmom : ∀ m : ℕ, Integrable (fun x : ℝ => x ^ m) μ)
    (n : ℕ) (P : ℕ → Polynomial ℝ)
    (hdeg : ∀ k ∈ Finset.Icc 1 (n + 1), (P k).natDegree = k - 1)
    (horth : ∀ i ∈ Finset.Icc 1 (n + 1), ∀ j ∈ Finset.Icc 1 (n + 1),
      ∫ x, (P i).eval x * (P j).eval x ∂μ = if i = j then 1 else 0) :
    ∃ a : ℝ,
      (∀ x y : ℝ, x ≠ y →
        ∑ k ∈ Finset.Icc 1 n, (P k).eval x * (P k).eval y =
          a * ((P (n + 1)).eval x * (P n).eval y - (P n).eval x * (P (n + 1)).eval y) / (x - y)) ∧
      ∀ x : ℝ,
        ∑ k ∈ Finset.Icc 1 n, (P k).eval x ^ 2 =
          a * ((P (n + 1)).derivative.eval x * (P n).eval x -
            (P n).derivative.eval x * (P (n + 1)).eval x) := by sorry

end NatureSLT.Kernels
