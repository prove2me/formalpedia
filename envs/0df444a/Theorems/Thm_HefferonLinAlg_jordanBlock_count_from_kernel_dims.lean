-- Prove2me | Theorems.Thm_HefferonLinAlg_jordanBlock_count_from_kernel_dims
-- name    : HefferonLinAlg.jordanBlock_count_from_kernel_dims
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T03:57:27.794281+00:00
-- url     : https://prove2.me/theorems/c95367a0-576c-4b71-aa9c-2227664b55b4
-- title:
--   Kernel dimensions of the powers determine the block counts
-- statement:
--   Let $A$ be a square complex matrix with a Jordan form given by block sizes $sz$ and eigenvalues $\lambda$, fix a scalar $\mu$, and write $d_r = \dim \ker (A - \mu I)^r$. Then the number of Jordan blocks of size exactly $r+1$ carrying the eigenvalue $\mu$ satisfies $$\#\{i : sz_i = r+1,\ \lambda_i = \mu\} + d_r + d_{r+2} \;=\; 2\,d_{r+1}.$$ Read as $\#= 2d_{r+1} - d_r - d_{r+2}$, this is the classical formula recovering the block structure from the kernel dimensions of the powers of $A - \mu I$; it is stated additively here because truncated subtraction on the naturals would silently weaken the claim. Because the right-hand side depends only on $A$ and $\mu$, every Jordan form of $A$ must have the same number of blocks of each size and eigenvalue — which is exactly why the Jordan block multiset is an invariant.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section III.2, Theorem 2.16, printed p. 434 — Hefferon states there that the number and the length of the strings is determined by the transformation; this is the standard kernel-dimension formula that makes that determinacy quantitative

import Mathlib
import Definitions.Def_HefferonLinAlg_jordan

open Matrix

namespace HefferonLinAlg

theorem jordanBlock_count_from_kernel_dims
    {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {sz : Fin k → ℕ} {lam : Fin k → ℂ}
    (h : IsJordanFormOf A sz lam) (mu : ℂ) (r : ℕ) :
    (Finset.univ.filter fun i => sz i = r + 1 ∧ lam i = mu).card
        + kerDim A mu r + kerDim A mu (r + 2)
      = 2 * kerDim A mu (r + 1) := by
  sorry

end HefferonLinAlg
