-- Prove2me | Theorems.Thm_GenSort_claim_3_11
-- name    : GenSort.claim_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:38:58.223515+00:00
-- url     : https://prove2.me/theorems/09d6937d-fb69-4eca-ad14-1d346ad7d845
-- title:
--   Claim 3.11 — one phase makes $O(n\log^3 n)$ queries
-- statement:
--   There is an absolute constant $C > 0$ such that the following holds. **Standing assumptions of §3.** $F \subseteq E(G)$ and $f = |F| > 2^{24} n \log^2 n$ (otherwise the routine queries all of $F$ and stops).
--
--   Across building the coarse estimator, the vertex flagging, and the $\log n$ rounds of error isolation, the total number of queries made is at most
--   $$
--   C\, n \log^3 n,
--   $$
--   on every outcome of the random choices.
--
--   Differences from the source:
--   - reading: the arbitrary choices of the page (σ, the split, ties, τ′) → every valid choice rule; reason: the page leaves them arbitrary; the universal reading is the stronger one
--   - reading: sample sizes, s, t, 2¹⁰ s log n and the number of passes log n (real numbers) → rounded up; reason: these are integers in the algorithm
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - reading: "we terminate prematurely" if fewer than s + 2¹⁰s log n bad edges are found → that pass ends with no edge removed; the pass queries all 16d(s + 2¹⁰s log n) sampled edges; reason: Claim 3.8's proof charges a failed pass at fraction 1 and Lemma 3.9 iterates passes; the budget is the page's
--   - encoding: the flagging sample from F → a uniform sample from the edges of H₀; reason: the edges of H₀ correspond one-to-one to the edges of F
--   - reading: the total number of queries made is bounded by O(n log³ n) → on every outcome of the phase; reason: the page's count is worst-case bookkeeping
--   - encoding: O(n log³ n) → ≤ C n log₂³ n with one absolute constant C chosen first; reason: the meaning of O(·) uniform in all instances
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: split the edges into groups of size at most d → exactly ⌈δ/d⌉ groups at a vertex of degree δ, for every such split; reason: groups of size at most d alone allow arbitrarily many copies, and the proof's count n + f/d needs ⌈δ/d⌉ groups
--   - encoding: vertices of H → pairs (original vertex, copy index) with copy index in Fin n; reason: a concrete representation of the copies
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.11, p.12 (PDF p.14), with the process of §3.1–§3.5, pp.5–10

import Mathlib
import Definitions.Def_GenSort_k0
import Definitions.Def_GenSort_dPar
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_tPar
import Definitions.Def_GenSort_AgreesOn
import Definitions.Def_GenSort_Split
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_TieRules_Valid
import Definitions.Def_GenSort_phasePMF

namespace GenSort

/-- **Claim 3.11** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.12, PDF p.14). Across building the coarse estimator, the vertex
flagging, and the `log n` rounds of error isolation, the total number of queries made is bounded
by `O(n log³ n)`.

**Formalization Note.** The bound holds on every outcome of the phase (every element of the
support of `phasePMF`), for every valid choice rule, with an absolute constant `C` chosen first.
`log` is `log₂`. The standing assumptions of §3 are hypotheses. -/
theorem claim_3_11 : ∃ C : ℝ, 0 < C ∧ ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hFG : (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet)
    (hf : (2 : ℝ) ^ 24 * n * Real.logb 2 n ^ 2 < F.card) (π : Equiv.Perm (Fin n)) (σr : (Fin (k0 n) → F) → Equiv.Perm (Fin n))
    (hσr : ∀ x i, AgreesOn π (σr x) (x i : Sym2 (Fin n)))
    (spr : (σ : Equiv.Perm (Fin n)) → Split F σ (dPar n F.card))
    (ρ : TieRules (Fin n × Fin n) (Fin n × Fin n) (sPar n (dPar n F.card)))
    (hρ : ρ.Valid Prod.fst Prod.fst π (tPar n (dPar n F.card))),
    ∀ o ∈ (phasePMF F π σr spr ρ).support, (o.queries : ℝ) ≤ C * n * Real.logb 2 n ^ 3 := by sorry

end GenSort
