-- Prove2me | Theorems.Thm_MTT_Eigenform_exists_oldform_dilation_expansion
-- name    : MTT.Eigenform.exists_oldform_dilation_expansion
-- status  : Open
-- author  : @riccardo.brasca
-- created : 2026-09-29T14:26:09.997703+00:00
-- url     : https://prove2.me/theorems/6eb58448-89aa-4c20-8531-2406e0373864
-- title:
--   Finite degeneracy expansion of a normalized old eigenform
-- statement:
--   Let $N,M>0$ and $k\ge2$. Let $f$ and $g$ be normalized algebraic cuspidal simultaneous prime Hecke and bad-prime $U$ eigenforms of levels $N$ and $M$, with the same weight and complex embedding. Suppose their prime coefficients and nebentypes agree outside finitely many primes, and $g$ has least positive level in that system.
--
--   There is a finite list of primes $q_i\mid N$ and complex numbers $\alpha_i$ such that
--
--   $$f(z)=\sum_{S\subseteq\{0,\ldots,r-1\}}\left(\prod_{i\in S}(-\alpha_i)\right)g\!\left(\left(\prod_{i\in S}q_i\right)z\right).$$
--
--   Writing $a_q(g)$ and $\varepsilon_g(q)$ for the embedded coefficient and character value, the parameters satisfy
--
--   $$\alpha_i=a_{q_i}(g)\quad(q_i\mid M),\qquad
--   \alpha_i^2-a_{q_i}(g)\alpha_i+\varepsilon_g(q_i)q_i^{k-1}=0\quad(q_i\nmid M).$$
--
--   This is an identity of actual holomorphic functions, independent of twists and $L$-values. Repeated primes, repeated roots, and the empty list are allowed. There is no additional scalar, since both first Fourier coefficients are one.
--
--   **Formalization Note.** Identifying the least-level representative with a primitive newform and deriving the displayed expansion are obligations of this open theorem. No local-root bound is asserted.
-- source:
--   Derived specialization of Atkin--Lehner--Li theory, rather than a verbatim statement: Stein, Modular Forms: A Computational Approach, Chapter 9, Theorem 9.4 (decomposition and multiplicity one), https://wstein.org/books/modform/modform/newforms.html. Ribet--Stein, Lectures on Modular Forms and Hecke Operators, Theorem 9.1.9 (printed p.74) and Section 9.2, equations (9.2.1)--(9.2.2) (printed p.76), https://wstein.org/books/ribet-stein/main.pdf. Solving the normalized simultaneous U-eigenvector equations in the degeneracy basis gives the product of linear corrections, expanded here over subsets. The already-published generic primitive basis theorem CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply is relevant infrastructure; the present result includes the MTT interface comparison and explicit eigenvector factorization.

import Definitions.Def_MTT_HeckeEquivalence

set_option autoImplicit false

open scoped BigOperators

/-- A normalized old eigenform is a product of linear degeneracy corrections of its
minimal-level representative, with each correction classified by the primitive local polynomial. -/
theorem MTT.Eigenform.exists_oldform_dilation_expansion
    {N M k : ℕ} (hN : 0 < N) (hM : 0 < M) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) (g : MTT.Eigenform M k ι)
    (hfg : f.SameHeckeSystem g) (hg : g.HasMinimalLevel) :
    ∃ (r : ℕ) (q : Fin r → ℕ) (a : Fin r → ℂ),
      (∀ i, (q i).Prime ∧ q i ∣ N ∧
        (if q i ∣ M then a i = ι (g.coeff (q i)) else
          (a i) ^ 2 - ι (g.coeff (q i)) * a i +
            ι (g.epsilon (q i)) * (q i : ℂ) ^ (k - 1) = 0)) ∧
      ∀ z : UpperHalfPlane,
        f.form z = ∑ S : Finset (Fin r), (∏ i ∈ S, -a i) *
          g.form (UpperHalfPlane.ofComplex ((∏ i ∈ S, (q i : ℂ)) * (z : ℂ))) := by
  sorry
