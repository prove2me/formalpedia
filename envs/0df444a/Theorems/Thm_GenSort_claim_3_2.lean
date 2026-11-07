-- Prove2me | Theorems.Thm_GenSort_claim_3_2
-- name    : GenSort.claim_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:31:01.216491+00:00
-- url     : https://prove2.me/theorems/24850fcf-7b9c-4f2a-ba56-f20cd1566773
-- title:
--   Claim 3.2 — the split bipartite graph has degrees $\le d$, at most $2n$ vertices per side, and $n \ge d > 2^{24}\log^2 n$, $f \le nd \le 2f$
-- statement:
--   **Standing assumptions of §3.** $F \subseteq E(G)$ and $f = |F| > 2^{24} n \log^2 n$ (otherwise the routine queries all of $F$ and stops).
--
--   Let $d = \lceil f/n \rceil$. Orient every edge of $F$ by a permutation $\sigma$, and build the bipartite graph $H$: each oriented edge $(u, v)$ joins a left copy of $u$ to a right copy of $v$, and at every vertex the edges are split into groups of size at most $d$, one copy of the vertex per group. Then:
--   1. every vertex of $H$ has degree at most $d$;
--   2. there are at most $2n$ left vertices and at most $2n$ right vertices;
--   3. $n \ge d > 2^{24} \log^2 n$ and $f \le nd \le 2f$.
--
--   These are the size and degree facts on which the parameters of the error isolation protocol rest.
--
--   Differences from the source:
--   - generalization: H is built from the coarse prediction σ of §3.1 → H is built from any permutation σ; reason: the construction and the claim use no property of σ; the coarse σ is a special case
--   - reading: split the edges into groups of size at most d → exactly ⌈δ/d⌉ groups at a vertex of degree δ, for every such split; reason: groups of size at most d alone allow arbitrarily many copies, and the proof's count n + f/d needs ⌈δ/d⌉ groups
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - encoding: vertices of H → pairs (original vertex, copy index) with copy index in Fin n, max(1, ⌈δ/d⌉) copies per side; reason: a concrete representation of the copies
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.2, p.6 (PDF p.8), with the construction of §3.2, p.6

import Mathlib
import Definitions.Def_GenSort_dPar
import Definitions.Def_GenSort_orient
import Definitions.Def_GenSort_Split
import Definitions.Def_GenSort_Hedges
import Definitions.Def_GenSort_copyVerts

namespace GenSort

/-- **Claim 3.2** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.2, p.6, PDF p.8). Let `F ⊆ E(G)` with `f = |F| > 2^24 n log² n`,
`d = ⌈f/n⌉`, `σ` a permutation, and `H` the bipartite graph built from the `σ`-oriented edges of
`F` by splitting the edges at each vertex into groups of size at most `d`. Then:
1. every vertex of `H` has degree at most `d`;
2. there are at most `2n` left vertices and `2n` right vertices;
3. `n ≥ d > 2^24 log² n` and `f ≤ nd ≤ 2f`.

**Formalization Note.** The split is any `Split F σ d`. A side's vertex set is `copyVerts` of that
side's degree function (`max(1, ⌈deg/d⌉)` copies per original vertex). `log` is `log₂`. -/
theorem claim_3_2 {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hFG : (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet)
    (hf : (2 : ℝ) ^ 24 * n * Real.logb 2 n ^ 2 < F.card) (σ : Equiv.Perm (Fin n)) (sp : Split F σ (dPar n F.card)) :
    (∀ x : Fin n × Fin n, ((Hedges sp).filter fun p => p.1 = x).card ≤ dPar n F.card ∧
      ((Hedges sp).filter fun p => p.2 = x).card ≤ dPar n F.card) ∧
    (copyVerts (fun u => ((orient F σ).filter fun q => q.1 = u).card) (dPar n F.card)).card ≤ 2 * n ∧
    (copyVerts (fun v => ((orient F σ).filter fun q => q.2 = v).card) (dPar n F.card)).card ≤ 2 * n ∧
    (dPar n F.card ≤ n ∧ (2 : ℝ) ^ 24 * Real.logb 2 n ^ 2 < dPar n F.card ∧
      F.card ≤ n * dPar n F.card ∧ n * dPar n F.card ≤ 2 * F.card) := by sorry

end GenSort
