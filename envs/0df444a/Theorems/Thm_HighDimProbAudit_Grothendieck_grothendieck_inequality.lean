-- Prove2me | Theorems.Thm_HighDimProbAudit_Grothendieck_grothendieck_inequality
-- name    : HighDimProbAudit.Grothendieck.grothendieck_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:37:29.218147+00:00
-- url     : https://prove2.me/theorems/6d05fa8b-ac1c-4a7f-9d43-d53600391172
-- title:
--   Theorem 3.5.1 — Grothendieck’s inequality, K ≤ 1.783
-- statement:
--   There is one real absolute constant $K$, independent of every dimension, matrix, Hilbert space and vector family below, with
--   $$0<K\le\frac{1783}{1000}.$$
--   For all $m,n\in\mathbb N$, let $A=(a_{ij})$ be a real $m\times n$ matrix. Suppose that for every pair of sign labelings $x_i,y_j\in\{-1,1\}$,
--   $$\left|\sum_{i,j}a_{ij}x_iy_j\right|\le1.$$
--   Then for every real Hilbert space $H$ and all vector families $u_1,\ldots,u_m$, $v_1,\ldots,v_n$ in $H$ with $\|u_i\|=\|v_j\|=1$,
--   $$\left|\sum_{i,j}a_{ij}\langle u_i,v_j\rangle\right|\le K.$$
--   The same constant applies to rectangular matrices of either sign and to infinite-dimensional Hilbert spaces. This compares sign-vector control with Hilbert-vector control at the numerical strength stated in the source. Empty row or column families have zero sums.
--
--   Differences from the source:
--   - encoding: row and column indices 1,…,m and 1,…,n → Fin m and Fin n; reason: a relabeling preserves all finite sums, including empty sums
--   - encoding: any Hilbert space in the surrounding real-vector setting → universe-polymorphic complete real inner product spaces; reason: this spells out the real convention used by the source’s Euclidean reduction without restricting dimension or separability
--   - encoding: an absolute constant K ≤ 1.783 → ∃ K : ℝ, 0 < K ∧ K ≤ 1783/1000 before all instance data; reason: the decimal is an exact rational; positivity is already forced by the normalized one-entry matrix, so it removes no instance
-- source:
--   Vershynin, High-Dimensional Probability: An Introduction with Applications in Data Science, Cambridge University Press, 2018, author-corrected electronic copy dated June 9, 2020, https://doi.org/10.1017/9781108231596, Theorem 3.5.1, printed p. 61 (PDF p. 69); the full-constant proof in §3.7, printed pp. 72–73 (PDF pp. 80–81).

import Mathlib

set_option autoImplicit false
universe uH

namespace HighDimProbAudit.Grothendieck

/-- Theorem 3.5.1, printed p. 61 / PDF p. 69, with its full numerical cap. -/
theorem grothendieck_inequality :
    ∃ K : ℝ, 0 < K ∧ K ≤ (1783 : ℝ) / 1000 ∧
      ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ),
        (∀ (x : Fin m → ℝ) (y : Fin n → ℝ),
          (∀ i, x i = -1 ∨ x i = 1) → (∀ j, y j = -1 ∨ y j = 1) →
            |∑ i, ∑ j, A i j * x i * y j| ≤ 1) →
        ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
          (u : Fin m → H) (v : Fin n → H),
          (∀ i, ‖u i‖ = 1) → (∀ j, ‖v j‖ = 1) →
            |∑ i, ∑ j, A i j * inner ℝ (u i) (v j)| ≤ K := by sorry

end HighDimProbAudit.Grothendieck
