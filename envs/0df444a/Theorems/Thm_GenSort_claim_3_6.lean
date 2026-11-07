-- Prove2me | Theorems.Thm_GenSort_claim_3_6
-- name    : GenSort.claim_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:29:18.968197+00:00
-- url     : https://prove2.me/theorems/2dd0f1e1-6ad9-4765-952d-9a0be90d4a65
-- title:
--   Claim 3.6 — with probability $\ge 15/16$ the pass's sample contains $s + 2^{10}s\log n$ bad edges
-- statement:
--   Let $H$ be the current bipartite graph, with at most $nd$ edges, and let $s$ be the §3.5 parameter. Suppose $H$ contains $w \ge n$ bad edges. Then, with probability at least $15/16$, among a sample of $16d \cdot (s + 2^{10} s\log n)$ edges drawn uniformly from $H$ with replacement, at least $s + 2^{10} s\log n$ are bad.
--
--   So the sampling step of a pass succeeds with constant probability whenever many errors remain.
--
--   Differences from the source:
--   - generalization: the current bipartite graph H of §3 → any finite bipartite instance with at most nd edges; reason: the proof uses only |E(H)| ≤ nd and w ≥ n, which every current graph of §3 satisfies
--   - reading: s = 2¹⁸n log n/d and 2¹⁰ s log n (real numbers) → rounded up; reason: §3.4 asks for positive integers
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - reading: there will be s + 2¹⁰s log n bad edges → at least s + 2¹⁰s log n bad edges; reason: the pass needs that many, and further ones are ignored
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.6, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_GenSort_badEdges
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_mPar
import Definitions.Def_GenSort_passSamples
import Definitions.Def_PunctSketch_coinProb

namespace GenSort

/-- **Claim 3.6** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.10, PDF p.12). Suppose the current graph `H` (at most `nd` edges)
contains `w ≥ n` bad edges. Then, with probability at least `15/16`, among the sample of
`16d · (s + 2^10 s log n)` edges drawn uniformly from `H` (with replacement) there are at least
`s + 2^10 s log n` bad edges.

**Formalization Note.** `s = sPar n d`, `2^10 s log n` is rounded up (`mPar n d`), `log` is `log₂`.
`|E(H)| ≤ nd` (used in the proof on the page) is a hypothesis. -/
theorem claim_3_6 {n d : ℕ} {L R : Type*} [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n))
    (hE : E.card ≤ n * d) (hw : n ≤ (badEdges E ℓ r π).card) :
    (15 / 16 : ℝ) ≤ PunctSketch.coinProb (Ω := Fin (passSamples n d) → E) fun y =>
      sPar n d + mPar n d ≤ (Finset.univ.filter fun i =>
        π.symm (r (y i : L × R).2) < π.symm (ℓ (y i : L × R).1)).card := by sorry

end GenSort
