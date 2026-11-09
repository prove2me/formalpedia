-- Prove2me | Theorems.Thm_GirthFiltering_RandomFiltering_approximate_girth_guarantee
-- name    : GirthFiltering.RandomFiltering.approximate_girth_guarantee
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:56:50.959608+00:00
-- url     : https://prove2.me/theorems/fa90899e-71fd-48d7-b5ae-069351ec1597
-- title:
--   Full random-filtering girth approximation and deterministic runtime
-- statement:
--   For every finite undirected input graph with arbitrary nonnegative real edge weights and no isolated vertices, the fixed charged Algorithm 1 has all of the following properties. The graph can be disconnected and may have labeled loops or parallel edges. Write $n,m$ for original input sizes and $g$ for its actual weighted girth.
--
--   There is one positive absolute implementation constant $C$, chosen before every graph, weight, sampling parameter, and failure probability. The fixed median-of-medians selector computes its specified order statistic in linear charged work. The tie-aware threshold routine computes the cycle bottleneck on every finite real label tape in linear work, without a distinctness assumption. Preprocessing returns the forest branch exactly when $g=+\infty$, and the zero-cycle branch exactly when $g=0$. Otherwise it constructs a positive core with $0<n'\le n$, $0<m'\le m$, preserving the zero-extended cycle bottleneck.
--
--   For every real $s>0$ and $0<\delta<1$, set $N=\lceil12e^s\ln(2/\delta)\rceil$ and $r=\lceil Ne^{-s}/2\rceil$. These satisfy $1\le r\le N$. All $N$ repetitions use independent continuous exponential labels. With $B'=8m'n'(2m'+1)$, $b=s+\ln B'$, and $\widehat T$ the $r$-th largest threshold, the returned value is $\widehat g=b/\widehat T$ on positive finite threshold outcomes. The exact confidence event obeys
--
--   $$
--   \Pr[s/g\le\widehat T\le b/g\text{ and }g\le\widehat g\le(1+\ln B'/s)g]
--   \ge1-2\exp(-Ne^{-s}/12)\ge1-\delta.
--   $$
--
--   The theorem also states $\Pr[g\le\widehat g\le(1+\ln(8mn(2m+1))/s)g]\ge1-\delta$ using original sizes. Forests return $+\infty$ deterministically; zero-girth graphs return zero deterministically. On every tape the actual charged cost is at most $C(m+1)N$ and at most $C(m+1)e^s\ln(2/\delta)$; empty input takes at most $C$ work.
--
--   For every real $k>1$, choose $s=\ln(8mn(2m+1))/(k-1)$. On every input with at least one edge the same program has the uniform cost envelope below, and on positive finite-girth input it is a $k$-approximation with probability at least $1-\delta$:
--
--   $$
--   C(m+1)[8mn(2m+1)]^{1/(k-1)}\ln(2/\delta).
--   $$
--
--   For each fixed $k,\delta$, some positive constant depending only on them bounds the cost by that constant times $m^{1+2/(k-1)}n^{1/(k-1)}$ on every input with at least one edge, forests and zero-girth graphs included. For each fixed $c>5$ and $\delta$, there are a positive constant and a vertex threshold depending only on $c,\delta$ such that, on every input with $m\le n^2$ beyond that threshold, $\ln\ln n>0$, $k(n)=c\ln n/\ln\ln n>1$, and the tuned program has deterministic cost $O(m(\ln n)^{5/c})$. Its accuracy on positive finite-girth input is again $k(n)$ with probability at least $1-\delta$.
--
--   These are claims about a fixed program and its defined work count, not an existential successful-estimator hypothesis. They include threshold equivalence, preprocessing correctness, and validity of all recursion and rank bounds as proof obligations.
--
--   **Formalization Note** Work is measured in a charged ideal-real RAM with exact exponential draws and elementary real scalar operations. It is independent of edge-weight magnitudes. The factor $m+1$ accommodates empty input and is equivalent to $O(m)$ for nonempty input. The paper provides no numeric implementation-time coefficient; $C$ is existential and absolute. The exponent $5/c$, the constants 8 and 12, the rank fraction $1/2$, and the failure exponent denominator 12 are unchanged.
--
--   Differences from the source:
--   - reading: the abstract says any real factor and Section 4 says k > 1 → every real k > 1, with natural logarithms and delta in (0,1); reason: Section 3.3 divides by k minus 1; the detailed Algorithm 1 uses log(2/delta), which is retained uniformly
--   - encoding: finite undirected weighted graphs, including multigraphs after contraction → the reused finite endpoint carrier with explicit undirectedness, nonnegativity and no-isolated-vertex predicates; reason: these are precisely the Section 1.2 conventions; connectedness, bounded weights and rationality are not imposed
--   - generalization: ordinary undirected input graphs, with loops and parallel edges explicitly retained after contraction → the main input may itself be any finite labeled undirected multigraph; reason: every simple input is included; the same weighted-cycle semantics and bounds apply to loops and parallel edges, and the n-only specialization still requires the original size bound
--   - encoding: zero-edge contraction followed by Algorithm 1 on the positive graph → an operational forest/zero-cycle/positive-core split with ENNReal-valued output and both exact core-size and derived original-size estimates; reason: keeps every loop and parallel edge and all zero-weight and forest instances; unused contracted vertices are deleted
--   - encoding: Algorithm 2 two-way recursion at the upper median → three-way strict-high, equal-level and strict-low recursion, with bottleneck equality and deterministic linear cost as conclusions; reason: the printed recursion repeats itself on a triangle with all labels equal; the three-way implementation returns the same bottleneck while shrinking on every recursive branch
--   - encoding: linear-time selection, graph traversals and ideal exact-real sampling in O notation → fixed median-of-medians, adjacency/DFS and contraction programs with charged sparse RAM blocks, exact exponential tape draws, and an absolute cost constant before inputs; reason: makes the stated operation model and constant dependence explicit; fuel sufficiency is a correctness conclusion and no graph or rank oracle is a primitive
--   - encoding: one-based rounded descending rank and the numerical quotient → ascending index N minus r with proved rank validity, and an explicit infinity return on nonpositive or infinite selected thresholds; reason: the exceptional branch has zero probability on positive-girth input under the stated continuous laws and avoids division-by-zero defaults
--   - encoding: O(mN), fixed-k time, and the large-factor asymptotic → a uniform C(m+1)N and exponential envelope, separate fixed-k constants, and c/delta-dependent constants and size thresholds for exponent 5/c; reason: the plus-one covers constant-time empty input; the tuned clauses take m ≥ 1 because s = ln(8mn(2m+1))/(k−1) is undefined at m = 0, and empty input is covered by the constant-time clause; no fixed-k constant is claimed uniform as k tends to 1; m ≤ n squared applies to original input sizes only
-- source:
--   Yablon, Approximating the Girth of an Undirected, Weighted Graph for Larger Approximation Factors, STOC 2027 submission #59 (2026), pinned PDF sha256 cf63df259cbd099089184755e2c32f0d51f00dea322509f35766f4a91a4e021f, p. 2, Section 1.1; p. 3, Algorithm 1 Ensure; pp. 4–5, Algorithm 2 and linear-work display; p. 7, Section 3.2 confidence, approximation and runtime displays; p. 8, Section 3.3 tuning displays; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/59.pdf

import Definitions.Def_GirthFiltering_RandomFiltering_Estimator
open scoped ENNReal

namespace GirthFiltering.RandomFiltering

/-- Full unnumbered headline guarantee: Algorithm 1 and Sections 3.2-3.3.
The one absolute implementation constant precedes every input and parameter.
Selection, threshold correctness, preprocessing, and charged deterministic
runtime are conclusions about the fixed program, never supplied as hypotheses. -/
theorem approximate_girth_guarantee :
    ∃ C : ℝ, 0 < C ∧
    -- Correctness and deterministic linear cost of the actual selector.
    (∀ (xs : List EReal) (k : ℕ), k < xs.length →
      IsOrderStatistic xs k (runCharged (select xs k)).1 ∧
      ((runCharged (select xs k)).2 : ℝ) ≤ C * (xs.length + 1 : ℕ)) ∧
    -- Algorithm 2 is the cycle bottleneck on every finite real label tape.
    (∀ (G : WeightedGraph), VehicleRoutingSurvey.Routing.Undirected G →
      ∀ X : Fin G.q → ℝ,
        (runCharged (findThreshold (edgeList G X))).1 =
          criticalThreshold G (fun e => (X e : EReal)) ∧
        criticalThreshold G (fun e => (X e : EReal)) = filterThreshold G X ∧
        (∀ t : ℝ, (t : EReal) ≤ criticalThreshold G (fun e => (X e : EReal)) ↔
          Survives G X t) ∧
        ((runCharged (findThreshold (edgeList G X))).2 : ℝ) ≤ C * (G.q + 1 : ℕ)) ∧
    (∀ (G : WeightedGraph), Admissible G →
      -- Exact preprocessing semantics, including every forest and zero cycle.
      ((runCharged (prepare G)).1 = .forest ↔ girth G = ⊤) ∧
      ((runCharged (prepare G)).1 = .zeroCycle ↔ girth G = 0) ∧
      ((runCharged (prepare G)).2 : ℝ) ≤ C * (G.q + 1 : ℕ) ∧
      (∀ (nv : ℕ) (es : List ActiveEdge),
        (runCharged (prepare G)).1 = .positive nv es →
        0 < nv ∧ es ≠ [] ∧ nv ≤ G.n ∧ es.length ≤ G.q ∧
        (∀ e ∈ es, 0 < e.weight) ∧
        (∀ X : Fin G.q → ℝ,
          (runCharged (do findThreshold (← sampleEdges G es X))).1 =
            criticalThreshold G (zeroExtendedLabels G X) ∧
          ((runCharged (do findThreshold (← sampleEdges G es X))).2 : ℝ) ≤
            C * (G.q + 1 : ℕ))) ∧
      (∀ (s δ : ℝ), 0 < s → 0 < δ → δ < 1 →
        1 ≤ sampleCount s δ ∧ 1 ≤ sampleRank s δ ∧
        sampleRank s δ ≤ sampleCount s δ ∧
        (∀ ω : Tape G (sampleCount s δ),
          (executionCost G s δ ω : ℝ) ≤ C * (G.q + 1 : ℕ) * (sampleCount s δ : ℝ) ∧
          (executionCost G s δ ω : ℝ) ≤
            C * (G.q + 1 : ℕ) * Real.exp s * Real.log (2 / δ)) ∧
        (G.q = 0 → ∀ ω : Tape G (sampleCount s δ),
          (executionCost G s δ ω : ℝ) ≤ C) ∧
        (girth G = ⊤ → ∀ ω, estimate G s δ ω = ⊤) ∧
        (girth G = 0 → ∀ ω, estimate G s δ ω = 0) ∧
        (0 < girth G ∧ girth G < ⊤ →
          ENNReal.ofReal (1 - δ) ≤ trialLaw G (sampleCount s δ)
            {ω | Accurate G (1 + Real.log (sizeFactor G.n G.q) / s)
              (estimate G s δ ω)}) ∧
        (∀ (nv : ℕ) (es : List ActiveEdge),
          (runCharged (prepare G)).1 = .positive nv es →
          (∀ᵐ ω ∂trialLaw G (sampleCount s δ),
            (0 : EReal) < selectedThreshold G s δ ω ∧
            selectedThreshold G s δ ω < ⊤) ∧
          (∀ ω, (0 : EReal) < selectedThreshold G s δ ω →
            selectedThreshold G s δ ω < ⊤ →
            estimate G s δ ω = ENNReal.ofReal
              ((s + Real.log (sizeFactor nv es.length)) /
                (selectedThreshold G s δ ω).toReal)) ∧
          MeasurableSet (confidenceEvent G s δ nv es.length) ∧
          ENNReal.ofReal (1 - 2 * Real.exp
            (-(sampleCount s δ : ℝ) * Real.exp (-s) / 12)) ≤
              trialLaw G (sampleCount s δ) (confidenceEvent G s δ nv es.length) ∧
          ENNReal.ofReal (1 - δ) ≤
            trialLaw G (sampleCount s δ) (confidenceEvent G s δ nv es.length)))) ∧
    -- Uniform tuned envelope for every REAL k > 1; original input sizes.
    (∀ (k δ : ℝ), 1 < k → 0 < δ → δ < 1 →
      ∀ (G : WeightedGraph), Admissible G → 0 < G.q →
        0 < tunedParameter G k ∧
        (0 < girth G ∧ girth G < ⊤ →
          ENNReal.ofReal (1 - δ) ≤ trialLaw G (sampleCount (tunedParameter G k) δ)
            {ω | Accurate G k (estimate G (tunedParameter G k) δ ω)}) ∧
        ∀ ω : Tape G (sampleCount (tunedParameter G k) δ),
          (executionCost G (tunedParameter G k) δ ω : ℝ) ≤
            C * (G.q + 1 : ℕ) *
              Real.rpow (sizeFactor G.n G.q) (1 / (k - 1)) * Real.log (2 / δ)) ∧
    -- Fixed-k constants may depend on k and delta, before the graph and weights.
    (∀ (k δ : ℝ), 1 < k → 0 < δ → δ < 1 →
      ∃ D : ℝ, 0 < D ∧ ∀ (G : WeightedGraph), Admissible G → 0 < G.q →
        ∀ ω : Tape G (sampleCount (tunedParameter G k) δ),
          (executionCost G (tunedParameter G k) δ ω : ℝ) ≤
            D * Real.rpow (G.q : ℝ) (1 + 2 / (k - 1)) *
              Real.rpow (G.n : ℝ) (1 / (k - 1))) ∧
    -- The full n-dependent large-factor specialization, exponent exactly 5/c.
    (∀ (c δ : ℝ), 5 < c → 0 < δ → δ < 1 →
      ∃ D : ℝ, 0 < D ∧ ∃ n₀ : ℕ, ∀ (G : WeightedGraph), Admissible G →
        n₀ ≤ G.n → G.q ≤ G.n ^ 2 →
        0 < Real.log (Real.log (G.n : ℝ)) ∧ 1 < highFactor G.n c ∧
        0 < tunedParameter G (highFactor G.n c) ∧
        (∀ ω : Tape G (sampleCount (tunedParameter G (highFactor G.n c)) δ),
          (executionCost G (tunedParameter G (highFactor G.n c)) δ ω : ℝ) ≤
            D * (G.q : ℝ) * Real.rpow (Real.log (G.n : ℝ)) (5 / c)) ∧
        (0 < girth G ∧ girth G < ⊤ →
          ENNReal.ofReal (1 - δ) ≤
            trialLaw G (sampleCount (tunedParameter G (highFactor G.n c)) δ)
              {ω | Accurate G (highFactor G.n c)
                (estimate G (tunedParameter G (highFactor G.n c)) δ ω)})) := by sorry

end GirthFiltering.RandomFiltering
