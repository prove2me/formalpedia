-- Prove2me | Theorems.Thm_GenSort_claim_3_3
-- name    : GenSort.claim_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:31:16.500061+00:00
-- url     : https://prove2.me/theorems/a7edff3f-150b-4fa3-ae28-8407cb7f6211
-- title:
--   Claim 3.3 — flagged vertices have $\ge d/(2^{24}\log^2 n)$ bad edges and unflagged ones $\le 4d/(2^{24}\log^2 n)$, w.p. $1 - n^{-10}$
-- statement:
--   **Standing assumptions of §3.** $F \subseteq E(G)$ and $f = |F| > 2^{24} n \log^2 n$ (otherwise the routine queries all of $F$ and stops).
--
--   Let $d = \lceil f/n \rceil$, and let $H$ be the bipartite graph of §3.2 built from a permutation $\sigma$ and a split. Take a new sample of $2^{32} n\log^3 n$ edges uniformly at random with replacement, query them, and flag a right vertex $v$ if at least $2^9\log n$ sampled edges incident to $v$ are bad. Then, with probability at least $1 - n^{-10}$:
--   1. every flagged vertex $v \in R$ is incident to at least $\dfrac{d}{2^{24}\log^2 n}$ bad edges;
--   2. every unflagged vertex $v \in R$ is incident to at most $\dfrac{4d}{2^{24}\log^2 n}$ bad edges.
--
--   The flagging step thus removes exactly the right vertices that are dense in errors, up to a factor of $4$.
--
--   Differences from the source:
--   - generalization: H is built from the coarse prediction σ of §3.1 → H is built from any permutation σ, the probability being over the flagging sample; reason: the claim's proof uses only the fresh sample, for σ fixed; the coarse σ is a special case
--   - reading: incident to most 4d/(2²⁴ log² n) → incident to at most 4d/(2²⁴ log² n); reason: typo on the page
--   - reading: sample size 2³²n log³ n → ⌈2³² n log₂³ n⌉; reason: a sample size is an integer
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - encoding: a new uniformly random sample from F → a uniform sample from the edges of H; reason: the edges of H correspond one-to-one to the edges of F
--   - encoding: v ∈ R → every pair (vertex, copy index), including pairs that are not vertices of H; reason: such pairs have no edges, are never flagged, and satisfy item 2 trivially
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: split the edges into groups of size at most d → exactly ⌈δ/d⌉ groups at a vertex of degree δ, for every such split; reason: groups of size at most d alone allow arbitrarily many copies, and the proof's count n + f/d needs ⌈δ/d⌉ groups
--   - encoding: with probability 1 − n⁻¹⁰ → probability at least 1 − n⁻¹⁰, as the fraction of sample sequences in E(H)^{k₀}; reason: i.i.d. uniform sampling with replacement is the uniform distribution on E(H)^{k₀}
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.3, p.7 (PDF p.9), with the flagging rule of §3.3, p.6

import Mathlib
import Definitions.Def_GenSort_k0
import Definitions.Def_GenSort_dPar
import Definitions.Def_GenSort_Split
import Definitions.Def_GenSort_Hedges
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_GenSort_flagged
import Definitions.Def_GenSort_FlagGood

namespace GenSort

/-- **Claim 3.3** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.3, p.7, PDF p.9). Let `F ⊆ E(G)` with `f = |F| > 2^24 n log² n`,
`d = ⌈f/n⌉`, and `H` the bipartite graph of §3.2 for a permutation `σ` and any split. Take a new
sample of `2^32 n log³ n` edges uniformly at random (with replacement) and flag `v ∈ R` if at least
`2^9 log n` sampled edges at `v` are bad. With probability at least `1 − n^{−10}`:
1. every flagged `v ∈ R` is incident to at least `d / (2^24 log² n)` bad edges;
2. every unflagged `v ∈ R` is incident to at most `4d / (2^24 log² n)` bad edges.

**Formalization Note.** The probability is over the flagging sample, for every `σ` and split.
Samples are drawn from the edges of `H`, which correspond one-to-one to `F`. The good event is
`FlagGood`. `log` is `log₂`. -/
theorem claim_3_3 {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hFG : (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet)
    (hf : (2 : ℝ) ^ 24 * n * Real.logb 2 n ^ 2 < F.card) (π σ : Equiv.Perm (Fin n)) (sp : Split F σ (dPar n F.card)) :
    1 - 1 / (n : ℝ) ^ 10 ≤ PunctSketch.coinProb (Ω := Fin (k0 n) → Hedges sp) fun z =>
      FlagGood (Hedges sp) Prod.fst Prod.fst π (dPar n F.card)
        (flagged (Hedges sp) Prod.fst Prod.fst π (k0 n) z) := by sorry

end GenSort
