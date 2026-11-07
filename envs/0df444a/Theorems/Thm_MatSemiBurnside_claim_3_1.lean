-- Prove2me | Theorems.Thm_MatSemiBurnside_claim_3_1
-- name    : MatSemiBurnside.claim_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:39:08.80839+00:00
-- url     : https://prove2.me/theorems/64f4d275-53b4-4d50-b457-d1ea96d31061
-- title:
--   Claim 3.1: equal-rank products split into at most $2^{d+2}$ single or rank-stable factors
-- statement:
--   Let $d$ be a positive integer and let $a_1,\dots,a_k\in\mathrm{Mat}_d(\mathbb Q)$, $k\ge1$, satisfy $\operatorname{rank}(a_1\cdots a_k)=\operatorname{rank}(a_i)$ for all $1\le i\le k$. Then $a_1\cdots a_k$ can be partitioned into at most
--   $$2^{d+2}$$
--   consecutive factors, each of which is either a single matrix among the $a_i$ or a product that is a rank-stable matrix.
--
--   This is the combinatorial input to Claim 3.2: a rank-preserving product is a bounded-length product of pieces, each either a generator or an element of a stable subsemigroup.
--
--   **Formalization Note** A partition into factors is a list of nonempty consecutive blocks whose concatenation is $[a_1,\dots,a_k]$.
--
--   Differences from the source:
--   - encoding: a partition of a_1 ⋯ a_k into factors → a list `ls` of nonempty blocks with `ls.flatten = l`; a single matrix is a block of length 1; reason: the same partitions
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, Claim 3.1, p.29 (also p.8)

import Mathlib
import Definitions.Def_MatSemiBurnside_IsStableSet
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Claim 3.1.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, Claim 3.1, p.29 (also p.8): "Let a1, . . . , ak ∈ Matd(ℚ) be such
that rank(a1 · · · ak) = rank(ai) for all 1 ≤ i ≤ k. Then a1 · · · ak can be partitioned into at most
2^(d+2) factors, each of which is either a single matrix among the ai's or a rank-stable matrix
product."

**Formalization Note.** The product is a nonempty list `l`; a partition into factors is a list of
nonempty consecutive blocks `ls` with `ls.flatten = l`; a block is "a single matrix" when it has
length one, and "a rank-stable matrix product" when its product is rank-stable. -/
theorem claim_3_1 {d : ℕ} (hd : 0 < d) (l : List (Matrix (Fin d) (Fin d) ℚ)) (hl : l ≠ [])
    (hrank : ∀ a ∈ l, l.prod.rank = a.rank) :
    ∃ ls : List (List (Matrix (Fin d) (Fin d) ℚ)), ls.flatten = l ∧ ls.length ≤ 2 ^ (d + 2) ∧
      ∀ b ∈ ls, b ≠ [] ∧ (b.length = 1 ∨ IsRankStable b.prod) := by sorry

end MatSemiBurnside
