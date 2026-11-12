-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_B_1
-- name    : MinCostArbPacking.Main.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:16.212572+00:00
-- url     : https://prove2.me/theorems/692c9f75-0943-4d60-8968-7da7a71d87a2
-- title:
--   Lemma B.1 — cyclic scans preserve reachability
-- statement:
--   **Lemma B.1 (Cyclic reachability).** Let $B=F_1\,\dot\cup\cdots\dot\cup\,F_k$ be a union of $k$ spanning trees of a vertex set $T$, and let $e\notin B$ have both ends in $T$. Keep only the following forest swaps: (a) $e$ scans its path in $F_1$; (b) if $k\ge2$, each element of $F_i$ scans its path in $F_{i+1}$ (indices modulo $k$). Then the elements of $B$ reachable from $e$ are exactly the elements of $B$ in the fundamental circuit of $e$ in $\mathcal G^k$.
--
--   It justifies scanning a single tree path per element in $D_{\mathrm{cmp}}$.
--
--   Differences from the source:
--   - encoding: the fundamental circuit of $e$ → every circuit of $\mathcal G^k$ contained in $B+e$; reason: unique, since $B+e$ is dependent
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), App. B, p.33, Lemma B.1

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_SearchGraph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma B.1 (Cyclic reachability), p.33: let `B = F₁ ∪̇ ⋯ ∪̇ F_k` be a union of `k` spanning trees
of a vertex set `T` and let `e ∉ B` have both ends in `T`. Keeping only the forest swaps in which
(a) `e` scans its path in `F₁`, and (b) if `k ≥ 2`, each element of `Fᵢ` scans its path in `F_{i+1}`
(indices mod `k`), the elements of `B` reachable from `e` are exactly the elements of `B` in the
fundamental circuit of `e` in `𝒢^k`. -/
theorem lemma_B_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (T : Finset V)
    (F : Fin k → Finset E) (hF : ∀ i, G.IsSpanningTreeOn (F i) T)
    (hdisj : ∀ i j, i ≠ j → Disjoint (F i) (F j)) (e : E)
    (he : e ∉ Finset.univ.biUnion F) (heT : G.tail e ∈ T ∧ G.head e ∈ T) :
    ∀ C, G.IsCircuitK k C → C ⊆ insert e (Finset.univ.biUnion F) →
      ∀ f ∈ Finset.univ.biUnion F,
        (Relation.ReflTransGen
            (fun x y => (x = e ∧ G.OnPath (F ⟨0, hk⟩) e y) ∨
              (2 ≤ k ∧ ∃ i, x ∈ F i ∧ G.OnPath (F (Digraph.cycNext i)) x y)) e f ↔
          f ∈ C) := by sorry

end MinCostArbPacking.Main
