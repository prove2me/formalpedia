-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_3_3
-- name    : MinCostArbPacking.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:27.894603+00:00
-- url     : https://prove2.me/theorems/d96c89f9-1354-403d-8ff8-39a5ec193615
-- title:
--   Lemma 3.3 — deficiency of a tight block
-- statement:
--   **Lemma 3.3 (Deficiency of a tight block).** Let $I$ be independent in $\mathcal G^k$ ($k\ge1$), with no arc entering $r$ and indegree at most $k$ at every other vertex, and let $T$ be $I$-tight. Then
--
--   $$\mathrm{def}_I(T)=k-\deg^{in}_I(T)\le k\quad\text{if } r\notin T,\qquad \mathrm{def}_I(T)=0\quad\text{if } r\in T.$$
--
--   It bounds the number of missing arcs in every block and drives the indegree bound after contraction (Lemma 4.6).
--
--   **Formalization Note** Deficiencies are integers.
--
--   Differences from the source:
--   - generalization: graphs from which loops and arcs entering $r$ have been deleted (§3.1) → arbitrary finite multigraphs (loops and arcs entering $r$ allowed); reason: the statement remains true without the deletion, and the deleted graph is a special case
--   - encoding: deficiency $\mathrm{def}_I$ → integer-valued `defi`/`defiSet`; reason: no truncated subtraction
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.2, p.8, Lemma 3.3

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 3.3, p.8: if the independent set `I` has no arc entering `r` and indegree at most `k` at
every other vertex, and `T` is `I`-tight, then `def_I(T) = k - deg^in_I(T) ≤ k` if `r ∉ T`, and
`def_I(T) = 0` if `r ∈ T`. -/
theorem lemma_3_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (I : Finset E)
    (hI : G.IndepK k I) (hr : G.inDeg I r = 0) (hdeg : ∀ v, v ≠ r → G.inDeg I v ≤ k)
    (T : Finset V) (hT : G.IsTight k I T) :
    (r ∉ T → G.defiSet k r I T = (k : ℤ) - (G.inDegSet I T : ℤ) ∧ G.defiSet k r I T ≤ k) ∧
      (r ∈ T → G.defiSet k r I T = 0) := by sorry

end MinCostArbPacking.Main
