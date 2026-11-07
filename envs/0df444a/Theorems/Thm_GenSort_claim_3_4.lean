-- Prove2me | Theorems.Thm_GenSort_claim_3_4
-- name    : GenSort.claim_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:31:49.781711+00:00
-- url     : https://prove2.me/theorems/3e1fdf26-5add-4f30-ab6c-a5265253b7bf
-- title:
--   Claim 3.4 — under the good events of Claims 3.1 and 3.3, flagging removes at most $f/16$ edges
-- statement:
--   **Standing assumptions of §3.** $F \subseteq E(G)$ and $f = |F| > 2^{24} n \log^2 n$ (otherwise the routine queries all of $F$ and stops).
--
--   Let $d = \lceil f/n\rceil$ and let $H$ be the bipartite graph of §3.2 built from a permutation $\sigma$ and a split. Assume the good event of Claim 3.1, $\mathrm{dist}_F(\pi, \sigma) \le f/(2^{28}\log^2 n)$, and the good event of Claim 3.3 for the flagging sample. Then the number of edges of $H$ incident to a flagged right vertex, which are the edges removed by flagging, is at most
--   $$
--   \frac{f}{16}.
--   $$
--
--   Differences from the source:
--   - generalization: σ is the coarse prediction of §3.1 satisfying the good event of Claim 3.1 → any permutation σ satisfying that event; reason: the proof uses only the event and the degree bound; the coarse σ is a special case
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: split the edges into groups of size at most d → exactly ⌈δ/d⌉ groups at a vertex of degree δ, for every such split; reason: groups of size at most d alone allow arbitrarily many copies, and the proof's count n + f/d needs ⌈δ/d⌉ groups
--   - encoding: vertices of H → pairs (original vertex, copy index) with copy index in Fin n; reason: a concrete representation of the copies
--   - reading: sample size 2³²n log³ n → ⌈2³² n log₂³ n⌉; reason: a sample size is an integer
--   - encoding: a new uniformly random sample from F → a uniform sample from the edges of H; reason: the edges of H correspond one-to-one to the edges of F
--   - reading: the good event of Claim 3.3: incident to most 4d/(2²⁴ log² n) → incident to at most 4d/(2²⁴ log² n); reason: typo on the page
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.4, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_GenSort_k0
import Definitions.Def_GenSort_dPar
import Definitions.Def_GenSort_Split
import Definitions.Def_GenSort_Hedges
import Definitions.Def_GenSort_CoarseGood
import Definitions.Def_GenSort_flagged
import Definitions.Def_GenSort_FlagGood

namespace GenSort

open Classical in
/-- **Claim 3.4** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.3, p.7, PDF p.9). Assuming the good events in Claim 3.1
(`dist_F(π, σ) ≤ f/(2^28 log² n)`) and Claim 3.3 (for the flagging sample `z`), the number of
edges of `H` removed by flagging (those incident to a flagged right vertex) is at most `f/16`.

**Formalization Note.** `H` is the graph of §3.2 for `σ` and any split; `log` is `log₂`. -/
theorem claim_3_4 {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hFG : (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet)
    (hf : (2 : ℝ) ^ 24 * n * Real.logb 2 n ^ 2 < F.card) (π σ : Equiv.Perm (Fin n)) (sp : Split F σ (dPar n F.card))
    (h31 : CoarseGood F π σ) (z : Fin (k0 n) → Hedges sp)
    (h33 : FlagGood (Hedges sp) Prod.fst Prod.fst π (dPar n F.card)
      (flagged (Hedges sp) Prod.fst Prod.fst π (k0 n) z)) :
    (((Hedges sp).filter fun p : (Fin n × Fin n) × (Fin n × Fin n) =>
      flagged (Hedges sp) Prod.fst Prod.fst π (k0 n) z p.2).card : ℝ) ≤ F.card / 16 := by sorry

end GenSort
