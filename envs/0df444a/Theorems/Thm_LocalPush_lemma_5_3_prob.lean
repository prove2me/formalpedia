-- Prove2me | Theorems.Thm_LocalPush_lemma_5_3_prob
-- name    : LocalPush.lemma_5_3_prob
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:54.540579+00:00
-- url     : https://prove2.me/theorems/e99f2f83-4b23-40a1-935e-914405ee196c
-- title:
--   Lemma 5.3, probability clause (other clauses: lemma_5_3) — $\Pr\{\mathcal G\}\ge1-\delta$: every SDD call of Algorithm 3 satisfies (6)
-- statement:
--   Let $(\Omega,\mu)$ be a probability space and $\mathrm{sol}(S,\omega)$ a solver that is measurable in the seed $\omega$ and whose call on any set $S\ni s$ satisfies (6) with probability at least $1-\lambda\delta$ (line 6 of Algorithm 3 calls the solver of Theorem 4.1 with failure probability $\lambda\delta$). Run Algorithm 3 with a fresh seed per call, the seeds independent with law $\mu$. Under the parameters of Algorithm 3 with $(\lambda+\eta)d(s)<1$, on a graph without isolated nodes, and for $\delta\in(0,1)$, the good event $\mathcal G$ that every invoked call satisfies (6) is measurable and
--   $$\Pr\{\mathcal G\}\ \ge\ 1-\delta.$$
--
--   This is the failure probability of Theorem 1.2.
--
--   Differences from the source:
--   - encoding: Pr{𝒢} for Algorithm 3 with the randomized solver of Theorem 4.1 → a seed model: sol : Finset V → Ω → (V → ℝ), measurable in the seed, called with fresh independent seeds (law Measure.infinitePi μ), each call on a set S ∋ s satisfying (6) with probability ≥ 1 − λδ; 𝒢 is also shown measurable; reason: the paper's probability space is that of the solver's internal randomness, independent across calls; Pr{𝒢} presupposes that 𝒢 is an event
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.3 and the event 𝒢, p.19 (PDF p.19)

import Mathlib
import Definitions.Def_LocalPush_SeedRun

open Finset Matrix MeasureTheory

namespace LocalPush

/-- **Lemma 5.3, `Pr{𝒢} ≥ 1 − δ`.**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.3, p.19 (PDF p.19).

"Next, let 𝒢 be the "good" event that every approximate SDD call invoked by Algorithm 3 satisfies the
guarantee (6). […] Lemma 5.3. We have Pr{𝒢} ≥ 1 − δ."

Let `(Ω, μ)` be a probability space and `sol : Finset V → Ω → (V → ℝ)` a solver, measurable in the seed, whose
call on any set `S ∋ s` satisfies (6) with probability at least `1 − λδ` (line 6 of Algorithm 3 calls the
solver with failure probability `λδ`; Theorem 4.1). Run Algorithm 3 with a fresh seed per call, the seeds
`ω 0, ω 1, …` independent with law `μ`. Under `Params`, on a graph without isolated nodes, and for
`δ ∈ (0, 1)`, the good event `𝒢` that every invoked call satisfies (6) is measurable and has probability at
least `1 − δ`.

**Formalization Note.** The solver is a measurable function of its seed, and the seeds of successive calls are
independent; the active set of call `i` depends on the earlier seeds. The clauses of Lemma 5.3 that hold on `𝒢`
are the separate milestone `LocalPush.lemma_5_3`. -/
theorem lemma_5_3_prob {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam η κ δ : ℝ) (hP : Params G s α lam η κ) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sol : Finset V → Ω → V → ℝ) (hsol : ∀ S, Measurable (sol S))
    (hcall : ∀ S : Finset V, s ∈ S →
      ENNReal.ofReal (1 - lam * δ) ≤ μ {ω | SolveGood G s α lam κ S (solOut sol S ω)}) :
    MeasurableSet (goodEvent G s α lam η κ sol) ∧
      ENNReal.ofReal (1 - δ) ≤ Measure.infinitePi (fun _ : ℕ => μ) (goodEvent G s α lam η κ sol) := by sorry

end LocalPush
