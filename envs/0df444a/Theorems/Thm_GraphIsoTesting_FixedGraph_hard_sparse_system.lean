-- Prove2me | Theorems.Thm_GraphIsoTesting_FixedGraph_hard_sparse_system
-- name    : GraphIsoTesting.FixedGraph.hard_sparse_system
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:34:28.270917+00:00
-- url     : https://prove2.me/theorems/b20fc48b-f6c5-4647-a064-587f342fcfb4
-- title:
--   Lemma 2.3 — Hard sparse system
-- statement:
--   There are a real constant $\delta>0$ and a natural size threshold $m_0$ such that for every even $m\ge m_0$ there exists a binary matrix $A$ with
--
--   $$A\in\mathbb F_2^{m\times(m/2)},\qquad
--   \operatorname{rowweight}(A)=3,\qquad\operatorname{columnweight}(A)=6,$$
--
--   and every set of at most $\delta m$ rows of $A$ is linearly independent over $\mathbb F_2$. The constants precede the equation-count quantifier and are independent of $m$ and $A$.
--
--   This is an existence conclusion, not a promise of the final graph theorem. It provides the exact sparse systems required by the degree-13 graph construction. In the final reduction the witness may be decreased to lie in $(0,1)$, preserving row independence.
--
--   Differences from the source:
--   - encoding: even equation count n and n/2 columns → Even m with natural division m / 2 and ZMod 2 entries; reason: division is exact under Even m, and every sufficiently large even count is retained
-- source:
--   Amit Dror, STOC 2027 submission #130 (October 2026), p. 5, Lemma 2.3; proof pp. 5–7

import Mathlib
import Definitions.Def_GraphIsoTesting_FixedGraph_BinarySystems

namespace GraphIsoTesting.FixedGraph

theorem hard_sparse_system :
    ∃ δ : ℝ, 0 < δ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → Even m →
      ∃ A : BinaryMatrix m (m / 2), Sparse36 A ∧
        IndependentRowsUpTo A (δ * (m : ℝ)) := by sorry

end GraphIsoTesting.FixedGraph
