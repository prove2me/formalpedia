-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_11
-- name    : MinorFreeSTC.Main.theorem_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:19:59.796504+00:00
-- url     : https://prove2.me/theorems/d1ceb420-1861-4dc6-a82b-8dab89b6fb4b
-- title:
--   Theorem 11 — (1+ϵ)-distortion spanning tree covers of size (2^{2^{O(r log r)}}/ϵ^{r+1})·(log log n + log(2/ϵ)), poly-time w.h.p.
-- statement:
--   There is a universal constant $c>0$ such that for every connected $n$-vertex $K_r$-minor-free weighted graph $G$ (weights in $[1,n^k]$) and every $\epsilon\in(0,1)$: **(E)** $G$ has a $(1+\epsilon)$-distortion spanning tree cover $\mathcal T$ with
--   $$|\mathcal T|\ \le\ \frac{2^{2^{c\,r\log_2r}}}{\epsilon^{r+1}}\Big(\log_2\log_2n+\log_2\frac2\epsilon\Big);$$
--   **(A)** for every $c'>1$ one admissible program, for all $r,k,\epsilon$ with constants $C,K$, computes such a cover from $(G,\epsilon,r)$ within $Cn^K+C$ steps, failing with coin-tape measure at most $n^{-c'}$.
--
--   This is the sharp form of the main theorem; Theorem 1 simplifies its bound (and §9.2 drops the aspect-ratio assumption).
--
--   **Formalization Note.** At $n=1$ the source's $\log\log 1$ is undefined; Lean's value is $\log_2\log_2 1=\log_2 0=0$.
--
--   Differences from the source:
--   - reading: 'we can, with high probability, construct in polynomial time' → for every c > 1 one program of the machine `Program` (the published SmaleNinth real-RAM core plus a fair `coin` and `roundUpPow`, rational literals), fixed before r, ϵ and the graph, every run of which halts within C·n^K + C steps (C, K depending only on the parameters named in the statement) and whose failure set of coin tapes has measure ≤ n^{−c}; reason: the paper names no machine; §9.2 (p. 53) lists the assumed operations, and p. 13 defines 'with high probability' as probability ≥ 1 − n^{−c} for a constant c that can be made arbitrarily large
--   - reading: 2^{O(r log r)} → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 52, Theorem 11

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

/-- **Theorem 11** (p. 52). There is a universal `c` such that every connected `K_r`-minor-free
weighted graph has, for every `ϵ ∈ (0, 1)`, a `(1 + ϵ)`-distortion spanning tree cover of size at
most `(2^{2^{c r log r}}/ϵ^{r+1}) · (log log n + log(2/ϵ))`, and for every `c' > 1` one program
computes one in `C n^K + C` steps with failure probability at most `n^{−c'}`. -/
theorem theorem_11 :
    ∃ c : ℝ, 0 < c ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ) (ϵ : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 0 < ϵ → ϵ < 1 →
        ∃ (m : ℕ) (T : Fin m → RamseyLST.Main.SpanningTree G),
          IsSpanningTreeCover G m T (1 + ϵ) ∧
            (m : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (c * r * Real.logb 2 r)) / ϵ ^ (r + 1) *
                (Real.logb 2 (Real.logb 2 (Fintype.card V)) + Real.logb 2 (2 / ϵ))) ∧
      ∀ c' : ℝ, 1 < c' → ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ (r k : ℕ) (ϵ : ℝ), 0 < ϵ → ϵ < 1 → ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (E : Encoding G),
            Connected G → MinorFree G r → AspectBounded G k →
            ComputesWHP A noOracle (E.cells ++ [ϵ, (r : ℝ)])
              (TreesOut E fun m T => IsSpanningTreeCover G m T (1 + ϵ) ∧
                (m : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (c * r * Real.logb 2 r)) / ϵ ^ (r + 1) *
                (Real.logb 2 (Real.logb 2 (Fintype.card V)) + Real.logb 2 (2 / ϵ)))
              (C * (Fintype.card V : ℝ) ^ K + C) ((Fintype.card V : ℝ) ^ (-c')) := by sorry

end MinorFreeSTC.Main
