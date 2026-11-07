-- Prove2me | Theorems.Thm_GenSort_claim_3_10
-- name    : GenSort.claim_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:37:30.929943+00:00
-- url     : https://prove2.me/theorems/beb9ae5e-3665-4003-b3c6-4dfe47142a9f
-- title:
--   Claim 3.10 — with probability $1 - 2/n^{10}$, flagging and the passes remove at most $f/2$ edges
-- statement:
--   **Standing assumptions of §3.** $F \subseteq E(G)$ and $f = |F| > 2^{24} n \log^2 n$ (otherwise the routine queries all of $F$ and stops).
--
--   Run one phase of §3 on $F$: the coarse sample and the coarse prediction $\sigma$, the bipartite graph $H$ (which initially contains $f$ edges), the flagging step, and $\log n$ error isolation passes. Then, with probability at least $1 - 2/n^{10}$ over all the samples of the phase, the flagging step and the subsequent $\log n$ passes together remove at most $f/2$ edges.
--
--   The postponed edges of a phase are the removed ones, so this is the size bound $|F'| \le |F|/2$ of Lemma 2.2 on all but a small-probability event.
--
--   Differences from the source:
--   - reading: the arbitrary choices of the page (σ, the split, ties, τ′) → every valid choice rule; reason: the page leaves them arbitrary; the universal reading is the stronger one
--   - reading: sample sizes, s, t, 2¹⁰ s log n and the number of passes log n (real numbers) → rounded up; reason: these are integers in the algorithm
--   - reading: log n with no base fixed → log₂ n; reason: the paper never fixes the base; every constant on the path was checked for base 2
--   - reading: "we terminate prematurely" if fewer than s + 2¹⁰s log n bad edges are found → that pass ends with no edge removed; the pass queries all 16d(s + 2¹⁰s log n) sampled edges; reason: Claim 3.8's proof charges a failed pass at fraction 1 and Lemma 3.9 iterates passes; the budget is the page's
--   - encoding: the flagging sample from F → a uniform sample from the edges of H₀; reason: the edges of H₀ correspond one-to-one to the edges of F
--   - encoding: with probability 1 − 2/n¹⁰ → probability at least 1 − 2/n¹⁰ under the distribution of the whole phase, before the fallback of §3.6; reason: the claim is what the fallback is applied to
--   - encoding: the vertex set V with a hidden ordering π → Fin n with a permutation π listing the vertices in increasing order, positions counted from 0; reason: a Lean convention that changes no instance
--   - reading: split the edges into groups of size at most d → exactly ⌈δ/d⌉ groups at a vertex of degree δ, for every such split; reason: groups of size at most d alone allow arbitrarily many copies, and the proof's count n + f/d needs ⌈δ/d⌉ groups
--   - encoding: vertices of H → pairs (original vertex, copy index) with copy index in Fin n; reason: a concrete representation of the copies
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), Claim 3.10, p.11 (PDF p.13), with the process of §3.1–§3.5, pp.5–10

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

/-- **Claim 3.10** (Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5, p.11, PDF p.13). Let `H` initially contain `f` edges. Then, with
probability at least `1 − 2/n^{10}`, the flagging step and the subsequent `log n` error isolation
passes together remove at most `f/2` edges.

**Formalization Note.** The probability is over the whole phase (`phasePMF`: coarse sample,
flagging sample, passes), before the fallback of §3.6, for every valid choice of `σ`, split, tie
rule and `τ'` rule. "Remove at most `f/2`" is `f − |Hf| ≤ f/2`, `f = |F| = |H₀|`. The standing
assumptions of §3 are hypotheses. -/
theorem claim_3_10 {n : ℕ} (G : SimpleGraph (Fin n)) (F : Finset (Sym2 (Fin n)))
    (hFG : (↑F : Set (Sym2 (Fin n))) ⊆ G.edgeSet)
    (hf : (2 : ℝ) ^ 24 * n * Real.logb 2 n ^ 2 < F.card) (π : Equiv.Perm (Fin n)) (σr : (Fin (k0 n) → F) → Equiv.Perm (Fin n))
    (hσr : ∀ x i, AgreesOn π (σr x) (x i : Sym2 (Fin n)))
    (spr : (σ : Equiv.Perm (Fin n)) → Split F σ (dPar n F.card))
    (ρ : TieRules (Fin n × Fin n) (Fin n × Fin n) (sPar n (dPar n F.card)))
    (hρ : ρ.Valid Prod.fst Prod.fst π (tPar n (dPar n F.card))) :
    ENNReal.ofReal (1 - 2 / (n : ℝ) ^ 10) ≤ (phasePMF F π σr spr ρ).toOuterMeasure
      {o | (F.card : ℝ) - o.Hf.card ≤ F.card / 2} := by sorry

end GenSort
