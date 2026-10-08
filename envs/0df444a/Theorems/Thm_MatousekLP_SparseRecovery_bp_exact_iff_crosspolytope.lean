-- Prove2me | Theorems.Thm_MatousekLP_SparseRecovery_bp_exact_iff_crosspolytope
-- name    : MatousekLP.SparseRecovery.bp_exact_iff_crosspolytope
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:39:23.960719+00:00
-- url     : https://prove2.me/theorems/3e022eca-a33b-465a-b004-61d163f8bf51
-- title:
--   Lemma 8.5.4 — reformulation of BP-exactness via the crosspolytope
-- statement:
--   Let $A$ be a real $m\times n$ matrix with $m<n$, let $r\le m$ be a nonnegative integer, and let $L=\{x\in\mathbb{R}^n: Ax=0\}$ be the kernel of $A$. Write $\|x\|_1=\sum_i|x_i|$, $\operatorname{supp}(x)=\{i: x_i\neq0\}$, and $B^n_1=\{x:\|x\|_1\le1\}$ for the crosspolytope. Recall that $A$ is BP-exact for $r$ if for every $b\in\mathbb{R}^m$, every solution $\tilde x$ of $Ax=b$ with at most $r$ nonzero components is the unique minimizer of $\|x\|_1$ subject to $Ax=b$. Then
--
--   $$A\text{ is BP-exact for } r\iff \text{for every } z\in\mathbb{R}^n \text{ with } \|z\|_1=1 \text{ and } |\operatorname{supp}(z)|\le r:\quad (L+z)\cap B^n_1=\{z\}.$$
--
--   In words: basis pursuit recovers every $r$-sparse solution exactly if and only if every translate of the kernel through a sparse boundary point $z$ of the crosspolytope touches the crosspolytope only at $z$. This geometric characterization is the starting point of the known proofs of Theorem 8.5.2.
--
--   **Formalization Note** The hypotheses $m<n$ and $r\le m$ are on the page and are kept, although the equivalence does not depend on them. Indices are $0,\dots,n-1$; the $\ell_1$-norm is written out as a sum of absolute values.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 172, Lemma 8.5.4 (Reformulation of BP-exactness); BP-exact defined p. 170

import Mathlib
import Definitions.Def_MatousekLP_SparseRecovery_BasisPursuit

namespace MatousekLP.SparseRecovery

open Matrix

/-- **Lemma 8.5.4 (Reformulation of BP-exactness)**, Matoušek & Gärtner, *Understanding and
Using Linear Programming*, Springer 2007, p. 172.  Let `A` be an `m × n` matrix, `m < n`, let
`r ≤ m`, and let `L = {x ∈ ℝⁿ : Ax = 0}` be the kernel of `A`.  Then `A` is BP-exact for `r`
if and only if for every `z ∈ ℝⁿ` with `‖z‖₁ = 1` and `|supp(z)| ≤ r`,
`(L + z) ∩ B₁ⁿ = {z}`. -/
theorem bp_exact_iff_crosspolytope {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (r : ℕ)
    (hmn : m < n) (hrm : r ≤ m) :
    IsBPExact A r ↔
      ∀ z : Fin n → ℝ, l1Norm z = 1 → (supp z).card ≤ r →
        translate (kernel A) z ∩ crosspolytope n = {z} := by sorry

end MatousekLP.SparseRecovery
