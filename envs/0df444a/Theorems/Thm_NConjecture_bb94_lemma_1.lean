-- Prove2me | Theorems.Thm_NConjecture_bb94_lemma_1
-- name    : NConjecture.bb94_lemma_1
-- status  : Proved
-- author  : @LG
-- created : 2026-11-22T00:44:08.632272+00:00
-- url     : https://prove2.me/theorems/42331223-9037-4e31-b8d4-882e52775edf
-- title:
--   Browkin–Brzeziński Lemma 1 (polynomial identity)
-- statement:
--   Browkin–Brzeziński's Lemma 1 (p. 933), the algebraic engine of their proof of Theorem 1: "For every $k\ge 0$, there exists a polynomial $f_k\in\mathbb Z[x]$ of degree $k$ with positive coefficients such that
--   $$\frac{x^{2k+1}-1}{x-1}=x^k\,f_k\!\left(\frac{(x-1)^2}{x}\right).$$"
--   Writing $f_k(z)=\sum_{j=0}^k s_j z^j$ with $s_j>0$ and expanding gives the equivalent polynomial identity (no denominators, since $j\le k$):
--   $$\sum_{i=0}^{2k} x^i=\sum_{j=0}^{k} s_j\,x^{k-j}(x-1)^{2j}.$$
--   The polynomial $f_k$ exists because $\frac{x^{2k+1}-1}{x-1}=\prod_{j=1}^k\big(x^2-2x\cos\tfrac{2\pi j}{2k+1}+1\big)=x^k\prod_{j=1}^k\big(\tfrac{(x-1)^2}{x}+2(1-\cos\tfrac{2\pi j}{2k+1})\big)$, whose factors have positive coefficients.
--
--   **Formalization Note.** The statement uses the cleared-denominator form, which is a polynomial identity in $\mathbb Z[x]$ equivalent to (3) of the source. `f.natDegree = k` and `∀ j ≤ k, 0 < f.coeff j` encode "degree $k$ with positive coefficients".
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf Lemma 1 p. 933, equation (3); proof and Remark 1 (explicit coefficients).

import Mathlib

namespace NConjecture

theorem bb94_lemma_1 (k : ℕ) :
    ∃ f : Polynomial ℤ, f.natDegree = k ∧ (∀ j ≤ k, 0 < f.coeff j) ∧
      (∑ i ∈ Finset.range (2 * k + 1), (Polynomial.X : Polynomial ℤ) ^ i) =
        ∑ j ∈ Finset.range (k + 1),
          Polynomial.C (f.coeff j) * Polynomial.X ^ (k - j) * (Polynomial.X - 1) ^ (2 * j) := by sorry

end NConjecture
