-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_1
-- name    : MinorFreeSTC.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:19:50.267679+00:00
-- url     : https://prove2.me/theorems/6bc0097d-1b98-4c17-91f3-d62e380e7422
-- title:
--   Theorem 1 — K_r-minor-free graphs have poly-time (1+ϵ)-distortion spanning tree covers of size (1/ϵ)^{r+2}·2^{r^{O(r)}}·log log n w.h.p.
-- statement:
--   Let $G=(V,E,w)$ be a finite connected weighted graph with positive weights, $n=|V|\ge1$, whose underlying simple graph has no $K_r$ minor, and let $\epsilon\in(0,1/2)$. A family of spanning trees of $G$ is a $(1+\epsilon)$-distortion spanning tree cover if every tree dominates $d_G$ and every pair $u,v$ has a tree with $d_T(u,v)\le(1+\epsilon)d_G(u,v)$.
--
--   There is a universal constant $c_0>0$ such that: **(E)** every such $G$ has a $(1+\epsilon)$-distortion spanning tree cover with $k$ trees, where
--   $$k\ \le\ \Big(\frac1\epsilon\Big)^{r+2}\cdot 2^{\,r^{c_0r}}\cdot\log_2\log_2 n;$$
--   and **(A)** for every $c>1$ there is one admissible program of the randomized real RAM (`Machine`) such that for all $r$ and $\epsilon\in(0,1/2)$ there are $C,K$ with: on every such $G$, given $(G,\epsilon,r)$ in the input layout, every run halts within $Cn^K+C$ steps, and the coin tapes on which it does not output such a cover of that size have measure at most $n^{-c}$. No bound on the aspect ratio of the weights is assumed.
--
--   This is the paper's main theorem: it brings the size of $(1+\epsilon)$-distortion spanning tree covers of minor-free graphs from $O(\log^2 n)$ down to $O(\log\log n)$ for fixed $r,\epsilon$. It is derived from Theorem 11 (p. 52) by simplifying the size bound, and §9.2 removes the aspect-ratio assumption.
--
--   **Formalization Note.** As printed the bound is $0$ at $n=2$ ($\log_2\log_2 2=0$) and the statement is false there (insight I1); it is stated as printed.
--
--   Differences from the source:
--   - reading: 'can be poly-time computed with high probability' → for every c > 1 one program of the machine `Program` (the published SmaleNinth real-RAM core plus a fair `coin` and `roundUpPow`, rational literals), fixed before r, ϵ and the graph, every run of which halts within C·n^K + C steps (C, K depending only on the parameters named in the statement) and whose failure set of coin tapes has measure ≤ n^{−c}; reason: the paper names no machine; §9.2 (p. 53) lists the assumed operations, and p. 13 defines 'with high probability' as probability ≥ 1 − n^{−c} for a constant c that can be made arbitrarily large
--   - reading: f(ϵ, r) = (1/ϵ)^{r+2} · 2^{r^{O(r)}} → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 2, Theorem 1 (restated p. 53)

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

/-- **Theorem 1** (Spanning Tree Covers for Minor-Free Graphs, p. 2, restated p. 53). There is a
universal `c₀` such that every connected `K_r`-minor-free weighted graph, for every `ϵ ∈ (0, 1/2)`,
has a `(1 + ϵ)`-distortion spanning tree cover of size at most
`(1/ϵ)^{r+2} · 2^{r^{c₀ r}} · log log n`, and for every `c > 1` one program computes such a cover
in `C n^K + C` steps with failure probability at most `n^{−c}`. -/
theorem theorem_1 :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r : ℕ) (ϵ : ℝ),
        Connected G → MinorFree G r → 0 < ϵ → ϵ < 1 / 2 →
        ∃ (k : ℕ) (T : Fin k → RamseyLST.Main.SpanningTree G),
          IsSpanningTreeCover G k T (1 + ϵ) ∧
            (k : ℝ) ≤ (1 / ϵ) ^ (r + 2) * (2 : ℝ) ^ ((r : ℝ) ^ (c₀ * r)) *
              Real.logb 2 (Real.logb 2 (Fintype.card V))) ∧
      ∀ c : ℝ, 1 < c → ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ (r : ℕ) (ϵ : ℝ), 0 < ϵ → ϵ < 1 / 2 → ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (E : Encoding G),
            Connected G → MinorFree G r →
            ComputesWHP A noOracle (E.cells ++ [ϵ, (r : ℝ)])
              (TreesOut E fun k T => IsSpanningTreeCover G k T (1 + ϵ) ∧
                (k : ℝ) ≤ (1 / ϵ) ^ (r + 2) * (2 : ℝ) ^ ((r : ℝ) ^ (c₀ * r)) *
                  Real.logb 2 (Real.logb 2 (Fintype.card V)))
              (C * (Fintype.card V : ℝ) ^ K + C) ((Fintype.card V : ℝ) ^ (-c)) := by sorry

end MinorFreeSTC.Main
