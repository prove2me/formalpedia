-- Prove2me | Theorems.Thm_MatSemiBurnside_proposition_7_cited
-- name    : MatSemiBurnside.proposition_7_cited
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:14.340633+00:00
-- url     : https://prove2.me/theorems/dd6620b9-c992-4e28-ac13-ee601a2b08c4
-- title:
--   [11, Proposition 7] (cited): equal-rank products have rank-stable factorisation trees of height $\le d+2$
-- statement:
--   Let $d$ be a positive integer and let $a_1,\dots,a_k\in\mathrm{Mat}_d(\mathbb Q)$, $k\ge1$, satisfy
--   $$\operatorname{rank}(a_1)=\cdots=\operatorname{rank}(a_k)=\operatorname{rank}(a_1\cdots a_k).$$
--   Then the product $a_1\cdots a_k$ has a factorisation tree of height at most $d+2$ in which every node with at least three children is labelled with a rank-stable matrix.
--
--   This is Proposition 7 of reference [11] of the paper (Ait El Manssour, Naraghi, Shirmohammadi, Worrell, SODA 2026). The paper uses it, in the proof of Claim 3.1, and does not prove it; the statement here follows the paper's own description of the result (pp.8 and 29). Its proof is the main external input of Theorem 1.
--
--   **Formalization Note** The hypothesis is written as "every $a_i$ has the rank of the full product", which is equivalent to the chain of equalities above.
--
--   Differences from the source:
--   - reading: "a factorisation tree" in the sense of Section 3 of [11] (not consulted) → `HasRSTree l (d + 2)`: the tree of p.7 (leaves a_1, …, a_k in order, internal nodes labelled by the product of their children, at least two children each) with the rank-stable condition of pp.8 and 29; reason: this paper's own description of [11]'s trees; nodes with one child add only height, so requiring two children loses no tree of bounded height
--   - encoding: rank(a_1) = ⋯ = rank(a_k) = rank(a_1 ⋯ a_k) → `∀ a ∈ l, a.rank = l.prod.rank` with `l ≠ []`; reason: the same condition
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Claim 3.1, p.29, citing [11, Proposition 7]; also p.8

import Mathlib
import Definitions.Def_MatSemiBurnside_HasRSTree
set_option autoImplicit false

namespace MatSemiBurnside

/-- **[11, Proposition 7], as cited (not proved in this paper).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of
Claim 3.1, p.29: "By [11, Proposition 7], with the definition of factorisation tree in Section 3 of
that paper, the product has a factorisation tree of height at most d + 2. At every node with at
least three children, the matrix labelling the node is rank-stable." p.8: "we have shown in
[11, Proposition 7] that if rank(a1) = · · · = rank(ak) = rank(a1 · · · ak) holds, such a tree can
be chosen with height at most d + 2."

This is a result of Ait El Manssour, Naraghi, Shirmohammadi, Worrell (SODA 2026), reference [11]
of the paper; the paper uses it and does not prove it. It is stated here from the paper's own
description of it.

**Formalization Note.** The product is a nonempty list `l` of matrices; the hypothesis is
"rank(a_i) = rank(a_1 ⋯ a_k) for all i" (as in Claim 3.1, equivalent to p.8's chain of
equalities). `HasRSTree l (d + 2)`: a factorisation tree of height at most d + 2 whose nodes with at
least three children carry rank-stable labels. -/
theorem proposition_7_cited {d : ℕ} (hd : 0 < d) (l : List (Matrix (Fin d) (Fin d) ℚ)) (hl : l ≠ [])
    (hrank : ∀ a ∈ l, a.rank = l.prod.rank) :
    HasRSTree l (d + 2) := by sorry

end MatSemiBurnside
