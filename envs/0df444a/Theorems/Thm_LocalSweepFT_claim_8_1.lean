-- Prove2me | Theorems.Thm_LocalSweepFT_claim_8_1
-- name    : LocalSweepFT.claim_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:38:37.904196+00:00
-- url     : https://prove2.me/theorems/bc4a7744-08cb-4cf3-9e5c-5e32d4b5fbfa
-- title:
--   Claim 8.1 — at most $\alpha^k$ connected subgraphs with fewer than $k$ edges contain a fixed vertex
-- statement:
--   For every $\Delta$ there is a constant $\alpha$ such that for every graph $G$ of maximum degree at most $\Delta+1$ (finite or infinite), every vertex $r$ and every $k$, the connected subgraphs of $G$ containing $r$ and having fewer than $k$ edges are finitely many, and their number is at most $\alpha^k$.
--
--   This counts the possible explanation trees rooted at a vertex, the entropy factor in the union bound of Lemma 6.2.
--
--   Differences from the source:
--   - generalization: a graph G = (V, E) and an integer k less than |E| → every locally finite graph of degree ≤ ∆ + 1 (possibly infinite) and every k ∈ ℕ; reason: the paper applies the claim to an infinite contour graph; finite graphs with k < |E| are a special case
--   - encoding: α a constant (σ on p.57, α on p.62) → α ∈ ℕ, chosen before the graph; reason: a real α can be rounded up
--   - encoding: "the number of connected subgraphs" → the set of such subgraphs is finite and its cardinality is at most α^k; reason: so that the count is meaningful
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…), Claim 8.1, p.62 (restated p.57)

import Mathlib

namespace LocalSweepFT

/-- Claim 8.1, p.62 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*, arXiv:2610.38847 (version of
November 3, 2026, sha256 85723eb5…)). Let `G = (V, E)` be a graph of maximum degree at most
`∆ + 1`, `k` an integer, and `r ∈ V`. There is a constant `α`, depending only on `∆`, such that the
number of connected subgraphs containing `r` and having fewer than `k` edges is at most `α^k`.

**Formalization Note.** Stated for every (possibly infinite) graph of degree at most `∆ + 1` and
every `k`; the printed range `k < |E|` for a finite graph is a special case (the paper applies the
claim to an infinite contour graph). The set of such subgraphs is shown finite, and `α` is chosen
before the graph. -/
theorem claim_8_1 (Δ : ℕ) : ∃ α : ℕ, ∀ {V : Type} (G : SimpleGraph V) [G.LocallyFinite],
    (∀ v, G.degree v ≤ Δ + 1) → ∀ (r : V) (k : ℕ),
      {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧ H.edgeSet.ncard < k}.Finite ∧
      {H : G.Subgraph | H.Connected ∧ r ∈ H.verts ∧ H.edgeSet.Finite ∧ H.edgeSet.ncard < k}.ncard
        ≤ α ^ k := by sorry

end LocalSweepFT
