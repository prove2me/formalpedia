-- Prove2me | Theorems.Thm_IncApproxVC_Oblivious_lemma_3_2
-- name    : IncApproxVC.Oblivious.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:42:38.092204+00:00
-- url     : https://prove2.me/theorems/0ea0cec8-3dab-4331-8adb-a946e5f8b327
-- title:
--   Lemma 3.2 — BiasedSample: $\lceil 10\log_2 n\cdot m/\nu\rceil$ uniform edge samples hit every set of out-volume $\ge\nu$ w.p. $\ge 1-n^{-10}$
-- statement:
--   Let $G=(V,E)$ be a simple directed graph with $n$ vertices and $m$ edges, and let $\nu>0$ be a volume parameter. Sample
--   $$N=\Big\lceil 10\log_2 n\cdot\frac{m}{\nu}\Big\rceil$$
--   edges of $G$ independently and uniformly at random, with replacement, and let $T$ be the set of their tails. Then for every set $A\subseteq V$ with $\mathrm{vol}^+_G(A)\ge\nu$,
--   $$\Pr[T\cap A\neq\emptyset]\ \ge\ 1-n^{-10}.$$
--   This is the sampling step that finds, with high probability, a vertex on the left side of a low-volume vertex cut (the "phase" of Algorithm 3).
--
--   **Formalization Note.** Sampling $N$ edges with replacement is the uniform distribution on sequences $\sigma\in E^N$, so the probability is the number of sequences containing an edge whose tail lies in $A$, divided by $m^N$.
--
--   Differences from the source:
--   - encoding: Pr over N edges sampled uniformly with replacement → the fraction of sequences σ : Fin N → E with some tail in A; reason: uniform sampling with replacement is the uniform law on E^N; same probability
--   - reading: a volume parameter ν → ν > 0 (real); reason: ν is a positive volume threshold; m/ν is undefined at ν = 0
-- source:
--   Adena, Henzinger, Rutschmann, Incremental Approximate Vertex Connectivity via Almost-Linear Time Local Cut Algorithms, STOC 2027 submission (manuscript sha256 d6baac6b…), p. 5, Lemma 3.2 (restated p. 23)

import Mathlib
import Definitions.Def_IncApproxVC_Oblivious_Digraph

namespace IncApproxVC.Oblivious

/-- **Lemma 3.2** (`BiasedSample(G, ν)`), p. 5 and p. 23. Sample `⌈10 log₂ n · m/ν⌉` edges of `G`
uniformly at random with replacement and let `T` be their tails. For every `A ⊆ V` with
`vol⁺_G(A) ≥ ν`, `Pr[T ∩ A ≠ ∅] ≥ 1 − n^{−10}`. Sampling with replacement is the uniform
distribution on sequences `σ : Fin N → E`, so the probability is the fraction of sequences that
contain an edge with tail in `A`. -/
theorem lemma_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : Digraph V) (hG : G.Loopless)
    (ν : ℝ) (hν : 0 < ν) (A : Finset V) (hA : ν ≤ (G.vol A : ℝ)) :
    ((Finset.univ.filter (fun σ : Fin ⌈10 * Real.logb 2 (Fintype.card V) *
          (G.numEdges : ℝ) / ν⌉₊ → G.edges => ∃ j, (σ j).1.1 ∈ A)).card : ℝ) /
        (Fintype.card (Fin ⌈10 * Real.logb 2 (Fintype.card V) * (G.numEdges : ℝ) / ν⌉₊ →
          G.edges) : ℝ) ≥
      1 - (Fintype.card V : ℝ) ^ (-10 : ℝ) := by sorry

end IncApproxVC.Oblivious
