-- Prove2me | Theorems.Thm_MISInducedMinor_alpha_GF_le
-- name    : MISInducedMinor.alpha_GF_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:20:53.506848+00:00
-- url     : https://prove2.me/theorems/013d753e-788c-4ffb-a40c-dc83638a34e4
-- title:
--   Proof of Lemma 3.2, pp.9–10 — the upper bound on $\alpha(G_F)$
-- statement:
--   For every graph $F$ with ordered vertices $v_1,\dots,v_n$,
--
--   $$\alpha(G_F)\ \le\ \mathrm{MaxCut}(F)+2\sum_{\substack{v_jv_{j'}\in E(F)\\ j<j'}}(j'-j);$$
--
--   that is, every independent set of $G_F$ has at most this many vertices.
--
--   Differences from the source:
--   - encoding: indices are 1-based: rows [2m], columns [2n − 1], vertex v_j in column 2j − 1 → 0-based: rows Fin (2m), columns Fin (2n − 1), vertex j − 1 : Fin n in column 2(j − 1); reason: Lean convention; the same graph up to the shift of indices, and Σ(j′ − j) is shift-invariant
--   - encoding: the vertices of F are ordered arbitrarily as v_1, …, v_n, and each edge e gets two reserved rows e_0, e_1 → F is a graph on Fin n with the order of Fin n, and edge number t of the lexicographic list of pairs a < b gets rows 2t (side 0) and 2t + 1 (side 1); reason: any vertex order is the order of Fin n after relabelling F, and the statement holds for every F; permuting rows is an automorphism of G, so the row assignment changes G_F only up to isomorphism
--   - encoding: MaxCut(F), the number of edges in a maximum-cardinality cut → the maximum over all A ⊆ V(F) of the number of pairs (a, b) ∈ A × Aᶜ with ab ∈ E(F); reason: each cut edge is exactly one such pair; the maximum is over a finite set, so it is attained
--   - encoding: ∑_{v_jv_j′ ∈ E(F), j<j′} (j′ − j) → the sum of b − a over the entries (a, b) of the canonical edge list, which have a < b; reason: natural-number subtraction is exact since a < b; the same number
--   - encoding: α(G_F) ≤ k → every independent set of G_F has at most k vertices; reason: the definition of α as a maximum
-- source:
--   Bonnet, Chang, Max Independent Set Remains NP-hard when Excluding a Planar Induced Minor (and More), arXiv:2609.11285 (sha256 e378b906…), proof of Lemma 3.2, pp.9–10

import Definitions.Def_MISInducedMinor_GF
import Definitions.Def_MISInducedMinor_maxCut
import Definitions.Def_MISInducedMinor_addTerm

set_option autoImplicit false

namespace MISInducedMinor

/-- **The upper bound of Lemma 3.2:** `α(G_F) ⩽ MaxCut(F) + 2 ∑_{vⱼvⱼ′ ∈ E(F), j < j′} (j′ − j)`,
i.e. every independent set of `G_F` has at most that many vertices. arXiv:2609.11285
(sha256 e378b906…), proof of Lemma 3.2, pp.9–10. -/
theorem alpha_GF_le (n : ℕ) (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (s : Finset ↥(keep F)) (hs : (GF F).IsIndepSet (s : Set ↥(keep F))) :
    s.card ≤ maxCut F + 2 * addTerm F := by sorry

end MISInducedMinor
