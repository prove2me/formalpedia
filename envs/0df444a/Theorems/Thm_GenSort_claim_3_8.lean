-- Prove2me | Theorems.Thm_GenSort_claim_3_8
-- name    : GenSort.claim_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:46.258801+00:00
-- url     : https://prove2.me/theorems/28b59eb1-b5c1-4b73-824b-b9d499ba1e53
-- title:
--   Claim 3.8 — if $w \ge n$, one pass leaves at most $w/4$ bad edges in expectation
-- statement:
--   Let $H$ be the current bipartite graph, with at most $2n$ left vertices and at most $nd$ edges, where $d > 2^{24}\log^2 n$, and run a single error isolation pass with the parameters of §3.5. Let $\tau'$ be the ordering whose candidate removal set $C_{\tau'}$ misses the fewest of the $2^{10}s\log n$ validation edges. If $H$ contains $w \ge n$ bad edges, then after the pass
--   $$
--   \mathbb E\big[\text{number of remaining bad edges in } H\big] \le \frac{w}{4}.
--   $$
--
--   Each pass thus removes three quarters of the errors in expectation while many remain.
--
--   Differences from the source:
--   - generalization: the current bipartite graph H of §3 → any finite bipartite instance with d > 2²⁴ log² n, at most 2n left vertices and at most nd edges; reason: the proof uses only these facts, which every current graph of §3 satisfies (Claim 3.2; removals only shrink H)
--   - reading: "we terminate prematurely" if fewer than s + 2¹⁰s log n bad edges are found → that pass ends with no edge removed; the pass queries all 16d(s + 2¹⁰s log n) sampled edges; reason: Claim 3.8's proof charges a failed pass at fraction 1 and Lemma 3.9 iterates passes; the budget is the page's
--   - reading: the expectation after a single pass → over the whole pass, a failed sampling step included; reason: the proof's accounting includes the failure probability 1/16
--   - reading: τ′ and the tie rule of step 4 → any minimizing ordering and any top-t selection; reason: the page leaves ties to arbitrary choice
--   - reading: s, t, 2¹⁰ s log n (real numbers) → rounded up; reason: §3.4 asks for positive integers
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.8, p.10 (PDF p.12), with the single pass of §3.5, pp.9–10

import Mathlib
import Definitions.Def_GenSort_badEdges
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_tPar
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_TieRules_Valid
import Definitions.Def_GenSort_passPMF

open scoped ENNReal

namespace GenSort

/-- **Claim 3.8** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.10, PDF p.12). Let `τ'` be the ordering whose candidate removal set
`C_τ'` misses the fewest of the `2^10 s log n` validation edges. If the current graph `H` contains
`w ≥ n` bad edges, then after a single pass
`E[number of remaining bad edges in H] ≤ w/4`.

**Formalization Note.** The expectation is over the whole pass, a failed sampling step included
(then nothing is removed). The context of §3 is carried as hypotheses:
`d > 2^24 log² n` (Claim 3.2), at most `2n` left vertices, at most `nd` edges; `s, t` are the
rounded §3.5 parameters; `ρ` is any valid tie rule and `τ'` rule. `log` is `log₂`. -/
theorem claim_3_8 {d : ℕ} {n : ℕ} {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n)) (hd : (2 : ℝ) ^ 24 * Real.logb 2 n ^ 2 < d)
    (hL : Fintype.card L ≤ 2 * n) (hE : E.card ≤ n * d)
    (ρ : TieRules L R (sPar n d)) (hρ : ρ.Valid ℓ r π (tPar n d))
    (hw : n ≤ (badEdges E ℓ r π).card) :
    ∑' o, passPMF E ℓ r π d ρ o * ((badEdges o.1 ℓ r π).card : ℝ≥0∞) ≤
      ((badEdges E ℓ r π).card : ℝ≥0∞) / 4 := by sorry

end GenSort
