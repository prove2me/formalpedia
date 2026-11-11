-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_bipartite_counting_sampling
-- name    : LogSupermodularBIS.Main.bipartite_counting_sampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:32:37.699264+00:00
-- url     : https://prove2.me/theorems/d990e25e-351b-4c0d-b88d-cd6152d1fe44
-- title:
--   Theorem 1.1 — approximate counting and nearly uniform sampling of bipartite independent sets in exp(O(n^{1/3} log^{4/3} n)) time
-- statement:
--   Write $I(G)$ for the independent sets of a graph $G$, $Z(G)=|I(G)|$, and $U_G$ for the uniform law on $I(G)$. There are randomized algorithms with the following guarantees for every bipartite graph $G$ with $n\ge2$ (labeled) vertices.
--   1. For every real $0<\eta\le1/2$, the sampling algorithm returns an independent set of $G$ whose law is within total variation distance $\eta$ of $U_G$. Its running time is at most
--   $$\exp\bigl(O(n^{1/3}\log^{4/3}n)\bigr)\,\mathrm{poly}(n,\log(1/\eta)).$$
--   2. For all reals $\epsilon,\delta\in(0,1/2]$, the counting algorithm returns an estimate $\widehat Z$ satisfying
--   $$\Pr\Bigl[\Bigl|\frac{\widehat Z}{Z(G)}-1\Bigr|\le\epsilon\Bigr]\ge1-\delta.$$
--   Its running time is at most
--   $$\exp\bigl(O(n^{1/3}\log^{4/3}n)\bigr)\,\mathrm{poly}(n,\epsilon^{-1},\log(1/\delta)).$$
--
--   Both bounds hold on every execution in the exact real-arithmetic model, and the sampler returns an independent set on every execution. The constants are absolute: the two programs, $C>0$ and the degree $a$ are chosen before $n$, $G$ and the accuracy parameters.
--
--   This is the first algorithm for #BIS on arbitrary bipartite graphs with a fixed-power saving in the exponent; it follows from Theorem 1.2 by summing out one side of the bipartition.
--
--   Differences from the source:
--   - encoding: a randomized algorithm in the exact real-arithmetic model with an O(·)/poly(·) running time on every execution → an existential Admissible program of the costed real RAM (rational literals; unit-cost arithmetic, comparisons, log, exp, uniform (0,1) draws; T_W per weight evaluation), chosen before all inputs, with a bound C·exp(C·X)·(1+params)^a on every tape in (0,1)^ℕ, C>0 and a∈ℕ absolute; reason: makes the uniform algorithm, the charged cost and the absolute constants of O(·) and poly(·) explicit; no instance is excluded
--   - reading: for every bipartite graph G (written G = (L, R, E) in the proof) → the input is n and the adjacency matrix of a 2-colorable simple graph on Fin n; no bipartition is supplied; reason: the stronger reading: the program must itself find a bipartition, which takes polynomial time
--   - encoding: the algorithms of Theorem 1.1 compute the weight (1.2) themselves → OracleFree programs run with the empty evaluator; reason: a graph algorithm has no weight oracle; every graph entry it reads is charged
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 2 (PDF 3), Theorem 1.1

import Definitions.Def_LogSupermodularBIS_Main_Algorithms

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Theorem 1.1 (Bipartite independent sets), p. 2. Two oracle-free programs chosen before the
graph and the accuracy parameters. Input: `n` and the adjacency matrix (no bipartition); the
sampler receives `η`, the counter `ε, δ`. -/
theorem bipartite_counting_sampling :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ S Cnt : Program, Admissible S ∧ Admissible Cnt ∧
      OracleFree S ∧ OracleFree Cnt ∧
      ∀ n : ℕ, 2 ≤ n → ∀ G : SimpleGraph (Fin n), G.Colorable 2 →
        (∀ η ∈ Set.Ioc (0 : ℝ) (1 / 2),
          SamplesWithin S noOracle (graphInput G [η]) n (uniformIndependent G) η
            (C * Real.exp (C * ((n : ℝ) ^ ((1 : ℝ) / 3) * Real.log n ^ ((4 : ℝ) / 3))) *
              (1 + n + Real.log (1 / η)) ^ a) ∧
          ∀ ω, ValidTape ω → ∀ x, outConfig S noOracle ω (graphInput G [η]) n = some x →
            IsIndependentConfig G x) ∧
        ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), ∀ δ ∈ Set.Ioc (0 : ℝ) (1 / 2),
          CountsWithin Cnt noOracle (graphInput G [ε, δ]) (numIndependentSets G) ε δ
            (C * Real.exp (C * ((n : ℝ) ^ ((1 : ℝ) / 3) * Real.log n ^ ((4 : ℝ) / 3))) *
              (1 + n + 1 / ε + Real.log (1 / δ)) ^ a) := by sorry

end LogSupermodularBIS.Main
