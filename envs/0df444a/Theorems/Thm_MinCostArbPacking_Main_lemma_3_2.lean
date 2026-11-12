-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_3_2
-- name    : MinCostArbPacking.Main.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:42:28.138202+00:00
-- url     : https://prove2.me/theorems/680f3d45-6849-47b3-b66d-962c7f8eca43
-- title:
--   Lemma 3.2 — free elements are exactly the crossing ones
-- statement:
--   **Lemma 3.2 (Free elements).** Let $I$ be independent in $\mathcal G^k$, $k\ge1$. An element $e\notin I$ is free (that is, $I+e\in\mathcal G^k$) if and only if it is crossing, i.e. its ends do not lie in a common tight block. If $e\notin I$ is internal to a tight block $T$, then its fundamental circuit (the circuit of $\mathcal G^k$ contained in $I+e$) lies in
--
--   $$I[T]+e.$$
--
--   This localizes exchanges to tight blocks and is used for the locality of shortest augmenting paths.
--
--   Differences from the source:
--   - generalization: graphs from which loops and arcs entering $r$ have been deleted (§3.1) → arbitrary finite multigraphs (loops and arcs entering $r$ allowed); reason: the statement remains true without the deletion, and the deleted graph is a special case
--   - encoding: its fundamental circuit → every circuit of $\mathcal G^k$ contained in $I+e$; reason: for independent $I$ and dependent $I+e$ there is exactly one such circuit
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §3.2, p.7, Lemma 3.2

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Graph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 3.2, p.7: for independent `I`, an element `e ∉ I` is free iff it is crossing; if `e` is
internal to a tight block `T`, its fundamental circuit (the circuit of `𝒢^k` inside `I + e`) lies in
`I[T] + e`. -/
theorem lemma_3_2 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (I : Finset E) (hI : G.IndepK k I) :
    (∀ e, e ∉ I → (G.Free k I e ↔ G.IsCrossing k I e)) ∧
      ∀ e T, e ∉ I → G.IsTightBlock k I T → G.tail e ∈ T → G.head e ∈ T →
        ∀ C, G.IsCircuitK k C → C ⊆ insert e I → C ⊆ insert e (G.induced I T) := by sorry

end MinCostArbPacking.Main
