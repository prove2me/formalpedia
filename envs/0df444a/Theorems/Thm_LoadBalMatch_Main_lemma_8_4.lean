-- Prove2me | Theorems.Thm_LoadBalMatch_Main_lemma_8_4
-- name    : LoadBalMatch.Main.lemma_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:35:06.464947+00:00
-- url     : https://prove2.me/theorems/275a5b59-b9e7-4830-b6a0-ce6518eea817
-- title:
--   Lemma 8.4 — for every $t\ge1$, w.p. $\ge1-t\,n^{-n}$, $\sum_e p^{(t)}_e\le 10t\,n\ln n$
-- statement:
--   Let $G$ be a graph on the finite set $V$ with $n=|V|$ and edge set $E$, and $\sigma$ an edge stream of $G$. Run Algorithm 4 with any admissible choices (which may depend on the past samples); $p^{(t)}_e$ is the sampling weight of $e$ at the start of iteration $t$ ($p^{(1)}_e=1/n$, doubled in every iteration in which $e$ violates the current fractional matching). Then for every $t\ge1$, with probability at least $1-t\cdot n^{-n}$ over the samples $R^{(1)},\dots,R^{(t-1)}$,
--   $$\sum_{e\in E}p^{(t)}_e\ \le\ 10t\cdot n\ln n .$$
--
--   Here $\ln$ is the natural logarithm. The bound controls the expected number of sampled edges, hence the space of Algorithm 4.
--
--   Differences from the source:
--   - generalization: Algorithm 4 with succinct x^(t+1) → every admissible choice rule, x^(t+1) any balanced fractional matching on the stabilized graph; reason: the proof uses neither succinctness nor the iteration count
--   - encoding: probability over the sampling in iterations 1, …, t − 1 → probAfter G P (t − 1) from the empty history, with sampling probabilities min{1, p}; reason: the sequential product law of the samples
--   - encoding: p^(t) defined by p^(1)_e = 1/n and doubling on violating edges → pAt: (1/n)·2^(number of earlier iterations in which e violates) on E, 0 off E; reason: the closed form of the doubling rule (p. 48)
--   - encoding: a graph G = (V, E) with n = |V| → a SimpleGraph on a finite type V, edges as Sym2 V, n = Fintype.card V; reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 47, Lemma 8.4

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_Algorithm4

namespace LoadBalMatch.Main

theorem lemma_8_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (σ : List (Sym2 V)) (hσ : IsEdgeStream G σ) (P : Alg4Choices V) (hP : P.Admissible G σ)
    (t : ℕ) (ht : 1 ≤ t) :
    1 - (t : ℝ) * ((Fintype.card V : ℝ) ^ Fintype.card V)⁻¹ ≤
      P.probAfter G (t - 1)
        (fun hs => ∑ e, P.pAt G hs e ≤
          10 * (t : ℝ) * (Fintype.card V : ℝ) * Real.log (Fintype.card V)) [] := by sorry

end LoadBalMatch.Main
