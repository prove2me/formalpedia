-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_4_mincut
-- name    : OneTwoThree.Weighting.lemma_4_mincut
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-13T09:18:54.23711+00:00
-- url     : https://prove2.me/theorems/18cc1a56-24f8-444b-9d34-dcbae71beb20
-- title:
--   Lemma 4 mincut — every s-t cut of G_{C,F,sigma} has capacity at least |sigma|
-- statement:
--   The min-cut half of Lemma 4 (Keusch, *A Solution to the 1-2-3 Conjecture*, arXiv:2303.02611v4, p. 4, Lemma 4; Lemma 2 in [18] = R. Keusch, Vertex-coloring graphs with 4-edge-weightings, Combinatorica 2023).
--
--   Let C = (S, T) be a maximum cut of G and let sigma be a side orientation of a set F of same-side edges. In the auxiliary network G_{C,F,sigma} every arc has capacity 1, so the capacity of an s-t cut A (src in A, snk not in A) is the number of arcs with tail in A and head outside A. Claim: every such cut has capacity at least |sigma|.
--
--   Proof sketch (Keusch's actual argument; no flow machinery): write X for the vertices of G lying in A. A sigma-edge (u, v) with u in X and v outside X contributes no sigma-arc to the cut, so it must be compensated by a cut-edge arc. Maximality applied to the symmetric-difference cut S' = S △ X gives: the number of cut edges with exactly one end in X is at least the number of same-side edges with exactly one end in X (edges with exactly one end in X flip their cut status under S -> S', and maximality forbids a net loss). Each sigma-edge oriented from X to its complement is a distinct same-side edge with exactly one end in X (sigma orients no edge twice), so the cut-edge arcs crossing from X contribute at least #{(u,v) in sigma : u in X, v not in X}; adding the sigma-arcs (s,u) with u not in X and (v,t) with v in X gives total at least |sigma| (the sigma-edge count splits into four X-membership cases, and the compensated case appears with multiplicity one extra).
--
--   Degenerate checks: A = {src} has capacity exactly |sigma| (all (s,u) arcs cross); A = all nodes except snk has capacity exactly |sigma| (all (v,t) arcs cross); sigma empty gives capacity >= 0 trivially.
--
--   On PUBLISHED this is the attackable unit of Lemma 4: it is provable by elementary Finset/SimpleGraph counting (maximality + the S △ X flip argument + sigma injectivity), with no flow machinery. The remaining gap to Lemma 4 itself is the max-flow/min-cut input (a separate sorry'd node); Lemma 3 stays blocked on that MFMCT gap — this child does not close Lemma 3 by itself.
--
--   Parent `OneTwoThree.Weighting.lemma_4` (`df7ed484-5818-483e-9772-6f83323a4673`) live-verified Open with `deprecated_at=null` immediately before posting; its binder is now `AuxArc G S sigma -> Nat` (the 2026-10-10 elab blocker is fixed). No `lemma_4_mincut` node exists in the mission yet (mission census 2026-10-13: 14 nodes, no duplicate).
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 4, Lemma 4 (Lemma 2 in [18] = R. Keusch, Vertex-coloring graphs with 4-edge-weightings, Combinatorica 2023) — min-cut half of the proof

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_STFlow
import Definitions.Def_OneTwoThree_Weighting_AuxNetwork

namespace OneTwoThree.Weighting

/-- Min-cut half of Lemma 4 (Keusch, arXiv:2303.02611v4, p. 4, Lemma 4; Lemma 2 of
Keusch, Combinatorica 2023). Every arc of `G_{C,F,σ}` has capacity `1`, so the capacity
of an `s`-`t` cut `A` (with `Node.src ∈ A`, `Node.snk ∉ A`) is the number of arcs with
tail in `A` and head outside `A`. Claim: every such cut has capacity at least `#σ`.

Proof idea (no flow machinery): write `X` for the vertices of `G` in `A`. Maximality
applied to the symmetric-difference cut `S △ X` shows the cut-edge arcs crossing from
`X` compensate every `σ`-edge oriented from `X` to its complement (each such `σ`-edge
is a distinct same-side edge with exactly one end in `X`, and `σ` orients no edge
twice); adding the `σ`-arcs `(s, u)` with `u ∉ X` and `(v, t)` with `v ∈ X` gives
`≥ #σ`. -/
theorem lemma_4_mincut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (hS : IsMaxCut G S) (σ : Finset (V × V))
    (hσ : IsSideOrientation G S σ) :
    ∀ A : Finset (Node V), Node.src ∈ A → Node.snk ∉ A →
      Finset.card σ ≤ Finset.card (Finset.univ.filter (fun a : AuxArc G S σ =>
        auxTail G S σ a ∈ A ∧ auxHead G S σ a ∉ A)) := by sorry

end OneTwoThree.Weighting
