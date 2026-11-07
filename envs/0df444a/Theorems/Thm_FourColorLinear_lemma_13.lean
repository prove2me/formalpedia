-- Prove2me | Theorems.Thm_FourColorLinear_lemma_13
-- name    : FourColorLinear.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:53:06.194202+00:00
-- url     : https://prove2.me/theorems/99732b96-eeb2-4b7a-8b69-782d6b2dff2e
-- title:
--   Lemma 13 — $|S_r(x)| = O((n(x)+b(x))/r)$
-- statement:
--   For each $A\ge0$ there is $C$ such that the following holds. Let $T$ be a binary tree satisfying the separator inequalities with threshold $n_1$, let $x$ be a node of $T$, and let $r$ satisfy $\max(1,n_1)\le r\le n(x)$. If
--   $$\sum_{z\in S_r(x)}n(z)\le n(x)+b(x)+A\,\frac{n(x)}{\sqrt r},$$
--   then
--   $$|S_r(x)|\le C\,\frac{n(x)+b(x)}{r}.$$
--
--   The lemma fills the gap the appendix finds in [15] and yields the bound $O(r_i/r_{i-1})$ on the number of children in Theorem 8.
--
--   Differences from the source:
--   - generalization: the binary subdivision of [15] → any binary tree with the inequalities of p.29 and the sum bound; reason: these are all the proof takes from the construction; the construction of [15] satisfies them
--   - reading: "|S_r(x)| = O(…)", no range of r in the display → n₁ ≤ r ≤ n(x), 1 ≤ r; reason: p.28: "For general x ∈ T and r ≤ n(x)"; the proof assumes n(y) "bigger than some large enough constant"; for r > n(x) the set is {x} and the bound fails
--   - generalization: "max{n(y₀), n(y₁)} … < 0.8n(y)" → ≤ 0.8·n(y) as the hypothesis; reason: the proof uses only the non-strict bound; trees with the strict bound are a case
-- source:
--   Inoue, Kawarabayashi, Miyashita, Mohar, Thomassen, Thorup, Four-Coloring Planar Graphs in Linear Time, arXiv:2610.39753 (held version, sha256 4dce39c5…), Lemma 13, p.28; proof pp.28–29

import Mathlib
import Definitions.Def_FourColorLinear_SepTree

namespace FourColorLinear

/-- Lemma 13 of arXiv:2610.39753 (held version, sha256 4dce39c5…), p.28: "|Sr(x)| = O((n(x) + b(x))/r)."

**Formalization Note** The hypotheses are what the proof on p.29 takes from [15] and from the shape of
the division: `IsSep`, and the inequality "Σ_{z∈Sr(x)} n(z) ≤ n(x) + b(x) + O(n(x)/√r)" with constant
`A`. `C` depends on `A` only. `r ≤ n(x)` is from p.28, "For general x ∈ T and r ≤ n(x)"; `n₁ ≤ r` is
the proof's "n(y) is bigger than some large enough constant". -/
theorem lemma_13 (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, ∀ (n₁ d r : ℕ) (x : SepTree), SepTree.IsSep n₁ d x → n₁ ≤ r → 1 ≤ r → r ≤ x.n →
      (((SepTree.Sr r x).map SepTree.n).sum : ℝ) ≤ x.n + x.b + A * x.n / Real.sqrt r →
      ((SepTree.Sr r x).length : ℝ) ≤ C * (x.n + x.b) / r := by sorry

end FourColorLinear
