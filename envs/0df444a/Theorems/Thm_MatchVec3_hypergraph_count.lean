-- Prove2me | Theorems.Thm_MatchVec3_hypergraph_count
-- name    : MatchVec3.hypergraph_count
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:27.985701+00:00
-- url     : https://prove2.me/theorems/7e1bbbf9-df82-48e9-97fd-8535f793d8bc
-- title:
--   Proof of Theorem 5.2: $|F|\le L\,\nu(F)\,\Delta(F)$
-- statement:
--   Let $L\ge1$ and let $F$ be an $L$-uniform hypergraph on $[K]$. Then
--
--   $$|F|\le L\,\nu(F)\,\Delta(F),$$
--
--   where $\nu(F)$ is the matching number and $\Delta(F)$ is the maximum vertex degree.
--
--   This is the first step of the recurrence: it reduces a fiber bound to bounds on the degree and the matching number.
--
--   Differences from the source:
--   - generalization: F an L-sum fiber, L > q → any L-uniform family on [K], L ≥ 1; reason: the argument uses only uniformity; L = 0 is excluded since F = {∅} has one edge and the right side is 0
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.14

import Mathlib
import Definitions.Def_MatchVec3_matchingNumber
import Definitions.Def_MatchVec3_maxDegree

namespace MatchVec3

/-- **The hypergraph count** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…),
proof of Theorem 5.2, p.14; also (2), p.5): `|F| ≤ L ν(F) ∆(F)` for an `L`-uniform hypergraph `F` on
`[K]`.

**Formalization Note** `F` is any `L`-uniform family, not only a fiber. `1 ≤ L` is needed: at `L = 0`,
`F = {∅}` has one edge and the right side is `0`. -/
theorem hypergraph_count {K L : ℕ} (hL : 1 ≤ L) (F : Finset (Finset (Fin K)))
    (hF : ∀ A ∈ F, A.card = L) :
    F.card ≤ L * matchingNumber F * maxDegree F := by sorry

end MatchVec3
