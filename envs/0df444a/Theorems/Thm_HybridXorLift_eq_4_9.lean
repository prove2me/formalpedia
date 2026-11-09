-- Prove2me | Theorems.Thm_HybridXorLift_eq_4_9
-- name    : HybridXorLift.eq_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:30.724197+00:00
-- url     : https://prove2.me/theorems/629f4b77-4534-45d5-bfea-78813907a6c4
-- title:
--   Eq. (4.9) — at most $\lfloor 100T/r \rfloor$ revealed blocks
-- statement:
--   Throughout, $n \ge 1$, $r \ge 1$, $q \ge 1$ are integers and $A$ is a parallel $q$-query hybrid algorithm on the $nr$ physical bits (the standing assumptions of Sections 3–5).
--
--   Let $T$ be the cost of $A$ and $a = 1/100$. For every history $h$ the revealed set $J(h) = \{i : w_i(h) \ge ar\}$ satisfies
--   $$
--   |J(h)| \le \Big\lfloor \frac{100\, T}{r} \Big\rfloor . \tag{4.9}
--   $$
--
--   The revealed sets bound the number of outer bits the classical simulator queries.
--
--   **Formalization Note** The floor is the natural-number quotient $\lfloor 100T / r\rfloor$.
--
--   Differences from the source:
--   - encoding: histories as sequences of outcomes, hy the child, v ≺ h the strict ancestors → lists of recorded outcomes (Step), h ++ [encodeStep y] the child, proper prefixes the strict ancestors; reason: the record determines the outcome (decodeStep ∘ encodeStep = some), so histories correspond one to one
--   - encoding: ⌊100T/r⌋ → the natural-number quotient 100 * T / r; reason: equal for r ≥ 1
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Eq. (4.9), p.15 (PDF p.17)

import Definitions.Def_HybridXorLift_revealed
import Definitions.Def_HybridXorLift_ParallelHybridAlg_cost
import Definitions.Def_HybridXorLift_ParallelHybridAlg_histories
import Definitions.Def_HybridXorLift_ParallelHybridAlg_SlotsAtMost

namespace HybridXorLift

/-- Eq. (4.9) of Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), p.15 (PDF p.17). With `a = 1/100` and `T` the cost of the algorithm,
`|J(h)| ≤ ⌊100 T / r⌋` for every history `h`.

**Formalization Note** The standing assumptions of §§3–5 (p.11 (PDF p.13): "we fix integers n ≥ 1, r ≥ 1, q ≥ 1 and a parallel q-query hybrid algorithm on nr physical bits") are explicit hypotheses. `⌊100T/r⌋` is the natural-number quotient `100 * T / r`, which is the
floor for `r ≥ 1`. -/
theorem eq_4_9 {n r : ℕ} {α : Type} (hn : 1 ≤ n) (hr : 1 ≤ r) (q : ℕ) (hq : 1 ≤ q)
    (A : ParallelHybridAlg (Fin n × Fin r) α) (hA : A.SlotsAtMost q)
    (h : List (Step (Fin n × Fin r))) (hh : h ∈ A.histories) :
    (revealed A h).card ≤ 100 * A.cost / r := by sorry

end HybridXorLift
