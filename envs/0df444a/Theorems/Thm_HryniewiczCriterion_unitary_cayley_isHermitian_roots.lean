-- Prove2me | Theorems.Thm_HryniewiczCriterion_unitary_cayley_isHermitian_roots
-- name    : HryniewiczCriterion.unitary_cayley_isHermitian_roots
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:47:27.626304+00:00
-- url     : https://prove2.me/theorems/43862e62-6b9c-475b-b709-01dba67d24c5
-- title:
--   The Cayley transform of a unitary matrix is Hermitian and carries its spectrum
-- statement:
--   Let $V$ be unitary and $|a|=1$ with $a$ not an eigenvalue of $V$. Then the Cayley transform
--   $$C\;=\;2ia\,(a-V)^{-1}-i\;=\;i\,(a+V)(a-V)^{-1}$$
--   is Hermitian, and the eigenvalues of $V$, with algebraic multiplicity, are
--   $$\lambda_k\;=\;a\,\frac{c_k-i}{c_k+i},$$
--   where $c_k$ are the (real) eigenvalues of $C$.
--   Proof idea: $(a-V)^{-*}=-aV(a-V)^{-1}$ gives $C^*=C$. From $(C+i)V=a(C-i)$ and $C=UDU^*$, $U^*VU$ is the diagonal matrix with entries $a(c_k-i)/(c_k+i)$, so $\chi_V=\prod_k(X-\lambda_k)$.
-- source:
--   Cayley transform between unitary and Hermitian matrices (classical); used to count eigenvalue crossings of positive unitary paths, cf. Hofer–Wysocki–Zehnder, The dynamics on three-dimensional strictly convex energy surfaces, Ann. of Math. 148 (1998), https://doi.org/10.2307/120994, proof of Theorem 3.4.

import Mathlib.Analysis.Matrix.Spectrum

open Matrix

theorem HryniewiczCriterion.unitary_cayley_isHermitian_roots {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n ℂ) (a : ℂ)
    (hV : star V * V = 1) (ha : star a * a = 1)
    (hdet : (a • (1 : Matrix n n ℂ) - V).det ≠ 0) :
    ∃ hC : ((2 * Complex.I * a) • (a • (1 : Matrix n n ℂ) - V)⁻¹ -
        Complex.I • (1 : Matrix n n ℂ)).IsHermitian,
      V.charpoly.roots = Multiset.map
        (fun k => a * (((hC.eigenvalues k : ℝ) : ℂ) - Complex.I) /
          (((hC.eigenvalues k : ℝ) : ℂ) + Complex.I)) Finset.univ.val := by sorry
