-- Prove2me | Theorems.Thm_HeldKarp_Gap_lemma_1
-- name    : HeldKarp.Gap.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:00.756798+00:00
-- url     : https://prove2.me/theorems/8fb805bb-fafe-4e17-bdfc-fe07149a8451
-- title:
--   Lemma 1 — a minimum tour stays minimum under the weights $c_{ij}+\pi_i+\pi_j$
-- statement:
--   Let $n\ge 3$, let $c_{ij}$ be real weights on the edges of the complete graph $K_n$, and let $\pi=(\pi_1,\dots,\pi_n)$ be a real $n$-vector. If $C^*$ is a minimum-weight tour with respect to the weights $c_{ij}$, then it is also a minimum-weight tour with respect to the weights $c_{ij}+\pi_i+\pi_j$:
--
--   $$
--   \sum_{\{i,j\}\in C^*} c_{ij}\le \sum_{\{i,j\}\in H} c_{ij}\ \text{ for all tours } H
--   \ \Longrightarrow\
--   \sum_{\{i,j\}\in C^*} (c_{ij}+\pi_i+\pi_j)\le \sum_{\{i,j\}\in H} (c_{ij}+\pi_i+\pi_j)\ \text{ for all tours } H.
--   $$
--
--   The lemma says that the transformation of the weights leaves the traveling-salesman problem invariant; it is what lets the gap function be rewritten in terms of the untransformed minimum tour weight $W$.
--
--   **Formalization Note** Vertices are `Fin n` and the weights a function on unordered pairs. A tour is the published `HeldKarp.Ascent.IsTour` (connected, every vertex of degree $2$). The hypothesis $3\le n$ is the paper's standing setting ($K_n$ has tours only for $n\ge 3$).
-- source:
--   Held & Karp, The Traveling-Salesman Problem and Minimum Spanning Trees, Operations Research 18(6) 1970, p. 1140, §1, Lemma 1

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
import Definitions.Def_HeldKarp_Gap_GapFunction

open Classical
open HeldKarp.Ascent

namespace HeldKarp.Gap

/-- **Lemma 1** (Held & Karp 1970, §1, p. 1140). If `C` is a minimum-weight tour with respect to
the edge weights `c_ij`, then it is also a minimum-weight tour with respect to the edge weights
`c_ij + π_i + π_j`. -/
theorem lemma_1 {n : ℕ} (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (C : SimpleGraph (Fin n)) (hC : IsTour C)
    (hmin : ∀ H : SimpleGraph (Fin n), IsTour H → weight c C ≤ weight c H) :
    ∀ H : SimpleGraph (Fin n), IsTour H → weight (shift c π) C ≤ weight (shift c π) H := by sorry

end HeldKarp.Gap
