-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_12
-- name    : MinCostArbPacking.Main.lemma_4_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:19.188604+00:00
-- url     : https://prove2.me/theorems/281ea472-f7cf-45bd-8feb-c2c478b2b14b
-- title:
--   Lemma 4.12 — forest-swap reachability and execution
-- statement:
--   **Lemma 4.12 (Forest-swap reachability and execution).** Fix a forest decomposition $I=F_1\,\dot\cup\cdots\dot\cup\,F_k$ ($k\ge1$) and let $e\notin I$.
--
--   1. $e$ is free iff it reaches a joining element by forest swaps.
--   2. If $e$ is nonfree, the elements of $I$ reachable from $e$ are exactly the elements of $I$ in its fundamental circuit.
--   3. If $e$ is nonfree, a path from $e$ to a reachable $f\in I$ with the fewest forest swaps yields a forest decomposition of
--   $$I-f+e$$
--   in which each forest keeps its connected components.
--
--   It replaces matroid-level exchange tests by forest swaps.
--
--   Differences from the source:
--   - generalization: the arborescence-packing setting of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ cheapest for its indegree vector, no arc of $I$ into $r$, indegree $\le k$) → an arbitrary finite multigraph and any $\mathcal G^k$-independent $I$ with a forest decomposition; reason: the proofs use only the forest decomposition (and extremality where stated); a loop has no forest swaps and is never free, an arc entering $r$ is an ordinary element; the reduced graph with the §4.2 invariants is a special case
--   - reading: "yields a forest decomposition of $I-f+e$" → the decomposition obtained by executing the swaps of the path (each $e_j$, $j\ge1$, replaced by $e_{j-1}$ in its forest), as in the proof in App. A; reason: this is the decomposition the source constructs and Algorithm 2 uses
--   - encoding: its fundamental circuit → every circuit of $\mathcal G^k$ contained in $I+e$; reason: unique for dependent $I+e$
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.3.1, p.15, Lemma 4.12 (proof App. A, p.33)

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_SearchGraph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.12 (Forest-swap reachability and execution), p.15, for a forest decomposition
`I = F₁ ∪̇ ⋯ ∪̇ F_k` and `e ∉ I`:
(a) `e` is free iff it reaches a joining element by forest swaps;
(b) if `e` is nonfree, the elements of `I` reachable from `e` are exactly the elements of `I` in its
fundamental circuit;
(c) if `e` is nonfree, a path from `e` to a reachable `f ∈ I` with the fewest forest swaps yields
(by executing its swaps) a forest decomposition of `I - f + e` in which each forest keeps its
connected components. -/
theorem lemma_4_12 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (I : Finset E)
    (F : Fin k → Finset E) (hF : G.ForestDecomp k I F) (e : E) (he : e ∉ I) :
    (G.Free k I e ↔ ∃ g, G.SwapReach F e g ∧ G.IsJoining F g) ∧
    (¬ G.Free k I e → ∀ C, G.IsCircuitK k C → C ⊆ insert e I →
      ∀ f ∈ I, (G.SwapReach F e f ↔ f ∈ C)) ∧
    (¬ G.Free k I e → ∀ f ∈ I, ∀ es, G.IsSwapPath F e f es →
      (∀ es', G.IsSwapPath F e f es' → es.length ≤ es'.length) →
        G.ForestDecomp k (insert e (I.erase f)) (Digraph.execSwaps F es) ∧
          ∀ i x y, (G.Conn (F i) x y ↔ G.Conn (Digraph.execSwaps F es i) x y)) := by sorry

end MinCostArbPacking.Main
