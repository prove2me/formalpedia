-- Prove2me | Theorems.Thm_MatSemiBurnside_claim_A_2
-- name    : MatSemiBurnside.claim_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:11.470748+00:00
-- url     : https://prove2.me/theorems/da050763-1fa1-4126-b045-566c60e4bcfb
-- title:
--   Claim A.2: rank-preserving products keep the first kernel and the last image
-- statement:
--   Let $d$ be a positive integer, $r\in\mathbb N$ and $a_1,\dots,a_k\in\mathrm{Mat}_d(\mathbb Q)$ with $k\ge1$; kernels and images are those of the row action.
--
--   1. If $a_1,\dots,a_k$ and their product $a_1\cdots a_k$ all have rank $r$, then for all $1\le i\le j\le k$
--   $$\operatorname{rank}(a_i\cdots a_j)=r,\qquad \ker(a_i\cdots a_j)=\ker(a_i),\qquad \operatorname{im}(a_i\cdots a_j)=\operatorname{im}(a_j).$$
--   2. Conversely, if all $a_i$ have rank $r$ and $\operatorname{rank}(a_ia_{i+1})=r$ for $1\le i<k$, then $a_1\cdots a_k$ has rank $r$.
--
--   These facts are used in all three of the paper's finiteness proofs: in the proof of Theorem 1 they show that a rank-preserving product is determined, up to a stable piece, by the kernel of its first factor and the image of its last.
--
--   **Formalization Note** The matrices are indexed by `Fin k` (from $0$); the factor $a_i\cdots a_j$ is the product of the consecutive slice of the list $[a_0,\dots,a_{k-1}]$ from position $i$ to position $j$.
--
--   Differences from the source:
--   - encoding: indices 1 ≤ i ≤ j ≤ k and the factor a_i ⋯ a_j → `Fin k` (0-based) and the list product of the slice `(drop i).take (j + 1 − i)`; reason: the same factors, renumbered from 0
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, Claim A.2, p.29

import Mathlib
import Definitions.Def_MatSemiBurnside_rowKer
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Claim A.2 (kernels and images of rank-preserving products).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix A, Claim A.2,
p.29: "If matrices a1, . . . , ak ∈ Matd(ℚ) and their product a1 · · · ak all have rank r, then, for
1 ≤ i ≤ j ≤ k, rank(ai · · · aj) = r, ker(ai · · · aj) = ker(ai), im(ai · · · aj) = im(aj).
Conversely, if all ai have rank r and rank(aiai+1) = r for 1 ≤ i < k, then their product has rank r."

**Formalization Note.** The matrices are a function `a : Fin k → Mat_d(ℚ)` with `k ≥ 1`, indexed from
0; the factor a_i ⋯ a_j (0-based `i ≤ j < k`) is the list product of `a i, …, a j`, i.e.
`((List.finRange k).drop i |>.take (j + 1 - i)).map a`. Row action kernels and images. -/
theorem claim_A_2 {d : ℕ} (hd : 0 < d) (r k : ℕ) (hk : 1 ≤ k) (a : Fin k → Matrix (Fin d) (Fin d) ℚ) :
    (((∀ i, (a i).rank = r) → (((List.finRange k).map a).prod.rank = r) →
      ∀ i j : Fin k, i ≤ j →
        let p := ((((List.finRange k).drop i.val).take (j.val + 1 - i.val)).map a).prod
        p.rank = r ∧ rowKer p = rowKer (a i) ∧ rowIm p = rowIm (a j)) ∧
    ((∀ i, (a i).rank = r) →
      (∀ i : Fin k, ∀ hi : i.val + 1 < k, (a i * a ⟨i.val + 1, hi⟩).rank = r) →
      ((List.finRange k).map a).prod.rank = r)) := by sorry

end MatSemiBurnside
