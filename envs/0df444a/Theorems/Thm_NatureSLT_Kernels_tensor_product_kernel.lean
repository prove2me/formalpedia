-- Prove2me | Theorems.Thm_NatureSLT_Kernels_tensor_product_kernel
-- name    : NatureSLT.Kernels.tensor_product_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:10.91901+00:00
-- url     : https://prove2.me/theorems/2fa1dce4-70e5-4739-bf3c-ac1ab53953ca
-- title:
--   Theorem 6.1 — the kernel of a tensor-product basis is the product of one-dimensional kernels
-- statement:
--   Let every coordinate of $x = (x^1, \dots, x^n)$ range over the same set $X$, and let $b_i$, $i \in \iota$, be a finite or infinite family of real **coordinatewise basis functions** on $X$, not necessarily orthonormal, whose one-dimensional kernel
--
--   $$K(s, t) = \sum_{i \in \iota} b_i(s)\, b_i(t)$$
--
--   converges for all $s, t \in X$. The $n$-dimensional basis (6.25) consists of the tensor products $b_{i_1, \dots, i_n}(x^1, \dots, x^n) = b_{i_1}(x^1) b_{i_2}(x^2) \cdots b_{i_n}(x^n)$ over all multi-indices $(i_1, \dots, i_n) \in \iota^n$. Then the kernel defining the inner product in this basis converges and is the product of one-dimensional kernels:
--
--   $$\sum_{(i_1, \dots, i_n) \in \iota^n} b_{i_1, \dots, i_n}(x)\, b_{i_1, \dots, i_n}(y) = \prod_{k=1}^{n} K(x^k, y^k).$$
--
--   This is how the book builds every multidimensional kernel of Chapter 6 (Hermite, spline and Fourier) from a one-dimensional one.
--
--   **Formalization Note** The left side is the sum over multi-indices of products of basis functions, not a definition of the multidimensional kernel as a product. "Converges" is unconditional summability in $\mathbb R$; for a finite family it is automatic. For $n = 0$ both sides equal $1$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 193, Theorem 6.1 (with Eq. (6.25))

import Mathlib

namespace NatureSLT.Kernels

/-- Theorem 6.1 (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §6.3.2, p. 193),
with the basis (6.25). Every coordinate `x^k` of `x = (x^1, …, x^n)` ranges over the same set `X`
(the book's interval `I`), and `b_i`, `i ∈ ι`, is a finite or infinite set of coordinatewise basis
functions on `X`, not necessarily orthonormal. The one-dimensional kernel is
`K(s, t) = Σ_i b_i(s) b_i(t)`, assumed convergent for all `s, t`. The `n`-dimensional basis
consists of the tensor products `b_{i₁ … iₙ}(x) = b_{i₁}(x^1) ⋯ b_{iₙ}(x^n)` over all multi-indices
`(i₁, …, iₙ) ∈ ιⁿ`, and the kernel defining the inner product in this basis,
`Σ_{i₁, …, iₙ} b_{i₁ … iₙ}(x) b_{i₁ … iₙ}(y)`, converges and equals the product of
one-dimensional kernels `Π_{k=1}^n K(x^k, y^k)`. -/
theorem tensor_product_kernel {X ι : Type*} (b : ι → X → ℝ)
    (hb : ∀ s t : X, Summable (fun i : ι => b i s * b i t)) (n : ℕ) (x y : Fin n → X) :
    Summable (fun I : Fin n → ι => (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k))) ∧
      ∑' I : Fin n → ι, (∏ k, b (I k) (x k)) * (∏ k, b (I k) (y k)) =
        ∏ k, ∑' i : ι, b i (x k) * b i (y k) := by sorry

end NatureSLT.Kernels
