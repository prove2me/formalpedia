-- Prove2me | Theorems.Thm_GenSort_lemma_3_9
-- name    : GenSort.lemma_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:34:52.3482+00:00
-- url     : https://prove2.me/theorems/91065ae0-740c-47ff-b6a3-13291ae9c1c3
-- title:
--   Lemma 3.9 — after $\log n$ passes, $O(n)$ bad edges remain in expectation
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. Let $H$ be the current bipartite graph with at most $n^2$ edges (and, as in Claim 3.8, at most $2n$ left vertices and at most $nd$ edges, where $d > 2^{24}\log^2 n$). Apply the single error isolation pass $\log n$ times, removing the selected set $C_{\tau'}$ from $H$ in each iteration. After these $\log n$ iterations,
--   $$
--   \mathbb E\big[\text{number of remaining bad edges in } H\big] \le C\, n .
--   $$
--
--   No good event is assumed: the expectation is unconditional.
--
--   Differences from the source:
--   - generalization: the current graph H of §3, with at most n² edges → any finite bipartite instance with at most n² edges, d > 2²⁴ log² n, at most 2n left vertices and at most nd edges; reason: the proof applies Claim 3.8, whose context these are, and every current graph of §3 satisfies them
--   - reading: log n times → ⌈log₂ n⌉ passes; reason: a number of iterations is an integer, and the base is fixed as everywhere
--   - reading: we terminate prematurely → that pass ends with no edge removed, and later passes still run; reason: the proof iterates Claim 3.8 over all passes
--   - reading: τ′ and the tie rule of step 4 → any minimizing ordering and any top-t selection; reason: the page leaves ties to arbitrary choice
--   - encoding: = O(n) → ≤ C n with one absolute constant C chosen before every other quantity; reason: the meaning of O(n) uniform in all instances
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: s, t, 2¹⁰ s log n (real numbers) → rounded up; reason: §3.4 asks for positive integers
--   - encoding: finite vertex sets L, R → finite types L, R in universe Type; reason: the constant C comes before L and R, so their universe must be fixed; every finite set has a copy in Type
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Lemma 3.9, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_GenSort_badEdges
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_tPar
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_TieRules_Valid
import Definitions.Def_GenSort_passesPMF

open scoped ENNReal

namespace GenSort

/-- **Lemma 3.9** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.11, PDF p.13). Let `H` be the current graph with at most `n²`
edges. Apply the single error isolation pass `log n` times, removing the selected set `C_τ'` from
`H` in each iteration. After these `log n` iterations,
`E[number of remaining bad edges in H] = O(n)`.

**Formalization Note.** `O(n)` is an absolute constant `C > 0`, chosen before every other
quantity. "`log n` times" is `⌈log₂ n⌉` passes. No good event is assumed. The context of Claim 3.8
(`d > 2^24 log² n`, at most `2n` left vertices, at most `nd` edges) is carried as
hypotheses. -/
theorem lemma_3_9 : ∃ C : ℝ, 0 < C ∧ ∀ {n d : ℕ} {L R : Type} [Fintype L] [DecidableEq L]
    [DecidableEq R] (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n)
    (π : Equiv.Perm (Fin n)), (2 : ℝ) ^ 24 * Real.logb 2 n ^ 2 < d →
    Fintype.card L ≤ 2 * n → E.card ≤ n * d → E.card ≤ n ^ 2 →
    ∀ ρ : TieRules L R (sPar n d), ρ.Valid ℓ r π (tPar n d) →
      ∑' o, passesPMF ℓ r π d ρ ⌈Real.logb 2 n⌉₊ E o * ((badEdges o.1 ℓ r π).card : ℝ≥0∞) ≤
        ENNReal.ofReal (C * n) := by sorry

end GenSort
