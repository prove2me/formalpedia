-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_10
-- name    : MinorFreeSTC.Main.theorem_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:19:54.708209+00:00
-- url     : https://prove2.me/theorems/468af4e1-2579-4091-9342-dd9051c3ea21
-- title:
--   Theorem 10 — a centered γ-growing hierarchy with γ ≥ c log n/ϵ embeds into O(1/ϵ) spanning trees with d_T ≤ (1+ϵ)·d^cent_H, poly-time w.h.p.
-- statement:
--   There are universal constants $c\ge1$ and $d>0$ such that the following holds. Let $G$ be a connected $n$-vertex weighted graph (weights in $[1,n^k]$; no minor-freeness), $\epsilon\in(0,1)$, and $H=(\mathcal C_0,\dots,\mathcal C_\kappa)$ a centered $\gamma$-growing hierarchical partition of $G$ with offset $\lambda>0$ and
--   $$\gamma\ \ge\ \frac{c\log_2 n}{\epsilon}.$$
--   **(E)** There is a family $\mathcal T$ of at most $d/\epsilon$ spanning trees of $G$ such that every $u,v$ have some $T\in\mathcal T$ with $d_T(u,v)\le(1+\epsilon)\,d^{\mathrm{cent}}_H(u,v)$. **(A)** For every $c'>1$ one admissible program, for all $k,\epsilon$ with constants $C,K$, computes such a family from $(G,\epsilon,\gamma,H)$ within $C((\kappa+1)n)^K+C$ steps, failing with coin-tape measure at most $n^{-c'}$.
--
--   This is the embedding step: each hierarchy of a centered hierarchy cover becomes $O(1/\epsilon)$ spanning trees.
--
--   Differences from the source:
--   - reading: 'we can, with high probability, construct in polynomial time' → for every c > 1 one program of the machine `Program` (the published SmaleNinth real-RAM core plus a fair `coin` and `roundUpPow`, rational literals), fixed before r, ϵ and the graph, every run of which halts within C·n^K + C steps (C, K depending only on the parameters named in the statement) and whose failure set of coin tapes has measure ≤ n^{−c}; reason: the paper names no machine; §9.2 (p. 53) lists the assumed operations, and p. 13 defines 'with high probability' as probability ≥ 1 − n^{−c} for a constant c that can be made arbitrarily large
--   - reading: O(1/ϵ) trees → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - reading: 'polynomial time' with the hierarchy H in the input → step bound C·((κ + 1)·n)^K + C; reason: (κ + 1)·n is the number of input cells holding H, which is not bounded by a function of n
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 40, Theorem 10

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_RamseyLST_Main_RamseySpanningTree
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Theorem 10** (p. 40). There are universal `c ≥ 1` and `d` such that for every connected
weighted graph `G`, `ϵ ∈ (0, 1)` and centered `γ`-growing hierarchical partition `H` of `G` with
offset `λ > 0` and `γ ≥ c log n/ϵ`, there is a family of at most `d/ϵ` spanning trees such that
every pair `u, v` has a tree with `d_T(u, v) ≤ (1 + ϵ) d^cent_H(u, v)`, and for every `c' > 1` one
program computes such a family from `(G, ϵ, γ, H)` in `C ((κ + 1) n)^K + C` steps with failure
probability at most `n^{−c'}`. -/
theorem theorem_10 :
    ∃ c d : ℝ, 1 ≤ c ∧ 0 < d ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (k : ℕ)
        (ϵ γ : ℝ) (H : Hierarchy V),
        Connected G → AspectBounded G k → 0 < ϵ → ϵ < 1 →
        IsCenteredGrowingHierarchy G H γ → c * Real.logb 2 (Fintype.card V) / ϵ ≤ γ →
        ∃ (m : ℕ) (T : Fin m → RamseyLST.Main.SpanningTree G),
          (m : ℝ) ≤ d / ϵ ∧ ∀ u v : V, ∃ i, (T i).dist u v ≤ ENNReal.ofReal (1 + ϵ) * centDist G H γ u v) ∧
      ∀ c' : ℝ, 1 < c' → ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ (k : ℕ) (ϵ : ℝ), 0 < ϵ → ϵ < 1 → ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (γ : ℝ)
            (H : Hierarchy V) (E : Encoding G),
            Connected G → AspectBounded G k →
            IsCenteredGrowingHierarchy G H γ → c * Real.logb 2 (Fintype.card V) / ϵ ≤ γ →
            ComputesWHP A noOracle (E.cells ++ [ϵ, γ] ++ E.hierCells H)
              (TreesOut E fun m T =>
                (m : ℝ) ≤ d / ϵ ∧ ∀ u v : V, ∃ i, (T i).dist u v ≤ ENNReal.ofReal (1 + ϵ) * centDist G H γ u v)
              (C * (((H.κ + 1) * Fintype.card V : ℕ) : ℝ) ^ K + C)
              ((Fintype.card V : ℝ) ^ (-c')) := by sorry

end MinorFreeSTC.Main
