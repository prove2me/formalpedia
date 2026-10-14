-- Prove2me | Theorems.Thm_OneTwoThree_Weighting_lemma_5_weight_reassignment
-- name    : OneTwoThree.Weighting.lemma_5_weight_reassignment
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-12T04:23:51.385093+00:00
-- url     : https://prove2.me/theorems/47d48d64-ea6c-4e26-ad64-aa5b71ae8db9
-- title:
--   Lemma 5 weight reassignment — {1,2,3}-weighting with prescribed weighted degrees on B
-- statement:
--   The weight-reassignment child of Lemma 5 (Keusch, *A Solution to the 1-2-3 Conjecture*,
--   arXiv:2303.02611v4, p. 6, proof of Lemma 5, stage (b)).
--
--   Given the parity subgraph E_o produced by child (a) — an edge set E_o with the
--   number of E_o-edges incident to v odd exactly on V_o := R' ∪ {v ∈ B : α(v) ≠ 2·deg(v)}
--   (the vertices that must end with odd weighted degree) — the proof reassigns weights
--   on the edges of E_o(v) for each v ∈ B: with α(v) = 2·deg(v) − 1, (|E_o(v)|+1)/2 of
--   those edges get weight 1 and the rest weight 3 (net 2·deg(v) − 1); with
--   α(v) = 2·deg(v) + 1, (|E_o(v)|−1)/2 get weight 1 and the rest 3 (net 2·deg(v) + 1);
--   with α(v) = 2·deg(v) (|E_o(v)| even), half get 1 and half 3 (net 2·deg(v)).
--   Edges outside E_o keep weight 2. Every E_o edge has exactly one B-endpoint (every
--   edge crosses the B/Bᶜ cut), so the per-B-vertex choices are consistent: s_ω(v) = α(v)
--   for v ∈ B (iii); for v ∈ R the incident E_o edges carry odd weights and the rest
--   weight 2, so s_ω(v) is odd iff |E_o(v)| is odd iff v ∈ R' (i) and (ii). The path-control
--   constraints (iv)–(vi) are refined by the sibling path-control node, not here.
--
--   Pure Finset-sum arithmetic — no flow machinery (the s-t network belongs to Lemma 4,
--   used by Lemma 3, not to any Lemma-5 child). The per-vertex 1/3-choice is the
--   Finset.exists_subset_card_eq construction (~100–150 lines to prove, no Mathlib gaps).
--   The exact E_o interface is pinned by the parity-subgraph child.
--
--   Parent `OneTwoThree.Weighting.lemma_5` (`18cd221d-d23a-4ae5-97c8-ca2db074a231`)
--   live-verified Open with `deprecated_at=null` immediately before posting.
-- source:
--   Keusch, A Solution to the 1-2-3 Conjecture, arXiv:2303.02611v4, p. 6, proof of Lemma 5 stage (b) (weight reassignment)

import Mathlib
import Definitions.Def_OneTwoThree_Weighting_Setting

namespace OneTwoThree.Weighting

/-- Weight reassignment child of Lemma 5 (Keusch, arXiv:2303.02611v4, p. 6,
proof of Lemma 5, stage (b)).

Given the parity subgraph `E_o` (child (a)): an edge set with the number of
`E_o`-edges incident to `v` odd exactly on
`V_o := R' ∪ {v ∈ B : α v ≠ 2 * G.degree v}`, there is a `{1,2,3}`-edge-weighting
`ω` with weighted degree `α v` at every `v ∈ B`, odd weighted degree on `R'`,
and even weighted degree off `B ∪ R'`. The per-`B`-vertex 1/3-choice is
consistent because every edge has exactly one `B`-endpoint (`hB`).
No flow machinery is involved. -/
theorem lemma_5_weight_reassignment {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : G.Connected) (B : Finset V)
    (hB : ∀ u v, G.Adj u v → (u ∈ B ↔ v ∉ B)) (α : V → ℕ)
    (hα : ∀ v ∈ B, (α v : ℤ) = 2 * (G.degree v : ℤ) - 1 ∨ (α v : ℤ) = 2 * (G.degree v : ℤ) ∨
      (α v : ℤ) = 2 * (G.degree v : ℤ) + 1)
    (R' : Finset V) (hR' : R' ⊆ Bᶜ)
    (E_o : Finset (Sym2 V)) (hE_o : (E_o : Set (Sym2 V)) ⊆ G.edgeSet)
    (hpar_e : ∀ v, Odd (Finset.card (E_o.filter (fun e => v ∈ e))) ↔
      v ∈ R' ∪ B.filter (fun u => α u ≠ 2 * G.degree u)) :
    ∃ ω : Sym2 V → ℕ, IsWeighting G 3 ω ∧
      (∀ v ∈ Bᶜ \ R', Even (wdeg G ω v)) ∧
      (∀ v ∈ R', Odd (wdeg G ω v)) ∧
      (∀ v ∈ B, wdeg G ω v = α v) := by sorry

end OneTwoThree.Weighting
