-- Prove2me | Theorems.Thm_MISInducedMinor_card_keep
-- name    : MISInducedMinor.card_keep
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:21:02.745174+00:00
-- url     : https://prove2.me/theorems/4e5cc044-0205-4c2f-810f-61fecba0f1db
-- title:
--   Proof of Corollary 1.6, p.11 — $|V(G_F)|=8\sum(j'-j)$
-- statement:
--   For every edge $e=v_jv_{j'}$ with $j<j'$, its two rows contribute exactly $8(j'-j)$ vertices to $G_F$. Therefore, for every graph $F$,
--
--   $$|V(G_F)|=8\sum_{\substack{v_jv_{j'}\in E(F)\\ j<j'}}(j'-j).$$
--
--   In particular $G_F$ has polynomially many vertices, as needed for the reduction of Theorem 1.5 ("Both $G$ and $G_F$ have $O(mn)$ vertices", p.7).
--
--   **Formalization Note** Only the equality is stated; the paper's continuation $\le 8m(n-1)\le12n(n-1)$ belongs to Corollary 1.6, and its second step assumes $F$ subcubic.
--
--   Differences from the source:
--   - generalization: F a simple subcubic graph (the proof of Corollary 1.6) → every graph F on Fin n; reason: the count uses no degree bound; the subcubic case is included
--   - encoding: indices are 1-based: rows [2m], columns [2n − 1], vertex v_j in column 2j − 1 → 0-based: rows Fin (2m), columns Fin (2n − 1), vertex j − 1 : Fin n in column 2(j − 1); reason: Lean convention; the same graph up to the shift of indices, and Σ(j′ − j) is shift-invariant
--   - encoding: the vertices of F are ordered arbitrarily as v_1, …, v_n, and each edge e gets two reserved rows e_0, e_1 → F is a graph on Fin n with the order of Fin n, and edge number t of the lexicographic list of pairs a < b gets rows 2t (side 0) and 2t + 1 (side 1); reason: any vertex order is the order of Fin n after relabelling F, and the statement holds for every F; permuting rows is an automorphism of G, so the row assignment changes G_F only up to isomorphism
--   - encoding: ∑_{v_jv_j′ ∈ E(F), j<j′} (j′ − j) → the sum of b − a over the entries (a, b) of the canonical edge list, which have a < b; reason: natural-number subtraction is exact since a < b; the same number
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), proof of Corollary 1.6, p.11

import Definitions.Def_MISInducedMinor_GF
import Definitions.Def_MISInducedMinor_addTerm

set_option autoImplicit false

namespace MISInducedMinor

/-- **The size of `G_F`:** for each edge `e = vⱼvⱼ′` with `j < j′`, its two rows contribute exactly
`8(j′ − j)` vertices to `G_F`, so `|V(G_F)| = 8 ∑_{vⱼvⱼ′ ∈ E(F), j < j′} (j′ − j)`.
arXiv:2609.11285 (sha256 e378b906…), proof of Corollary 1.6, p.11. -/
theorem card_keep (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    Nat.card ↥(keep F) = 8 * addTerm F := by sorry

end MISInducedMinor
