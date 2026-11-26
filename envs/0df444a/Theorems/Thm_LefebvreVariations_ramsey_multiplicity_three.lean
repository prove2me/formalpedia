-- Prove2me | Theorems.Thm_LefebvreVariations_ramsey_multiplicity_three
-- name    : LefebvreVariations.ramsey_multiplicity_three
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-25T23:48:53.527252+00:00
-- url     : https://prove2.me/theorems/78c38ed1-21eb-5ec6-82a9-23060fa0b608
-- title:
--   Lefebvre's variations, No. 61 — on a theme by Erdős, Burr and Rosta: the Ramsey multiplicity conjecture at k equals three
-- statement:
--   For every $n\in\mathbb{N}$ and every $2$-colouring of the edges of the complete graph $K_n$, the number of $3$-element monochromatic vertex sets, together with the vertex sets all of whose pairs have the second colour, is at least
--   $$
--   \frac{1}{2^{\binom32}}\binom n3=\frac18\binom n3 .
--   $$
--
--   This is the Ramsey multiplicity conjecture at $k=3$: every $2$-colouring of $K_n$ contains at least $2^{-\binom k2}\binom nk$ monochromatic copies of $K_k$ (Erdős; Burr and Rosta). For $k=3$ it is a consequence of Goodman's count of monochromatic triangles.
--
--   **Formalization Note** The statement copies the parent's formalization with `k = 3`: the colouring is `col : Sym2 (Fin n) → Bool` and the counted family is `{S : Finset (Fin n) | S.card = 3 ∧ (all pairs of S have colour true) ∨ (all pairs of S have colour false)}`. Because `∧` binds tighter than `∨`, the second alternative is *not* restricted to `S.card = 3`: the family contains the empty set, the singletons and every set of any size whose pairs are all `false`, besides the monochromatic triples. The inequality is therefore weaker than the true $k=3$ statement for small $n$; for $n\ge8$ it already holds for the monochromatic triples alone.
--
--   **Why this is a variation.** Variation on the open ramsey_multiplicity_conjecture (every 2-colouring of K_n has at least 2^(-C(k,2)) C(n,k) monochromatic copies of K_k). It is the case k = 3, the first non-trivial clique size, stated as the parent formalizes it; it is a special case in which the counting by Goodman applies, and a first test of the parent's formal statement.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   The Ramsey multiplicity conjecture: P. Erdos, On the number of complete subgraphs contained in certain graphs, Magyar Tud. Akad. Mat. Kutato Int. Kozl. 7 (1962), 459-464, and S. A. Burr and V. Rosta, On the Ramsey multiplicities of graphs (cited from memory; pages and details not re-checked). The case k = 3 follows from A. W. Goodman, On sets of acquaintances and strangers at any party, Amer. Math. Monthly 66 (1959), 778-783, which gives at least n(n-1)(n-5)/24 monochromatic triangles (cited from memory). Origin of this statement: the platform theorem ramsey_multiplicity_conjecture (Open) at k = 3, copying its formalization including its precedence of /\ over \/. Truth check performed independently: n(n-1)(n-5)/24 >= C(n,3)/8 for n >= 8, and for n <= 7 the empty set and the n singletons already give 1 + n >= C(n,3)/8.

import Mathlib

namespace LefebvreVariations

/-- The Ramsey multiplicity conjecture (Erdős; Burr and Rosta) at `k = 3`: every `2`-colouring of the
edges of `K_n` has at least `2^(-C(3,2)) · C(n,3)` monochromatic triangles. The statement is the parent's
with `k = 3`, including its reading of `∧` over `∨`: the second alternative (all pairs of `S` have
colour `false`) carries no condition on `|S|`, so the counted family also contains the empty set, the
singletons and the `false`-cliques of every size. For `n ≥ 8` the bound already holds for the monochromatic
triples alone, by Goodman's theorem (at least `n(n-1)(n-5)/24` of them).
Source: Goodman, "On sets of acquaintances and strangers at any party", Amer. Math. Monthly 66 (1959),
778-783 (cited from memory); the conjecture is in Erdős, "On the number of complete subgraphs contained
in certain graphs", Magyar Tud. Akad. Mat. Kutató Int. Közl. 7 (1962), 459-464 (cited from memory). -/
theorem ramsey_multiplicity_three :
    ∀ (n : ℕ) (col : Sym2 (Fin n) → Bool),
      (1 : ℝ) / 2 ^ (Nat.choose 3 2) * Nat.choose n 3 ≤
        {S : Finset (Fin n) | S.card = 3 ∧
          (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
            col (Sym2.mk a b) = true) ∨
          (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
            col (Sym2.mk a b) = false)}.ncard := by
  sorry

end LefebvreVariations
