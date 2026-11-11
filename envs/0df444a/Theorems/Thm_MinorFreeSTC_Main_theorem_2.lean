-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_2
-- name    : MinorFreeSTC.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:19:46.937443+00:00
-- url     : https://prove2.me/theorems/e1a932fc-c6c0-43e6-bc3a-cbf468b8c143
-- title:
--   Theorem 2 — K_r-minor-free graphs have ∆-diameter strong ((log n)^{2^{O(r log r)}}, 2^{2^{O(r log r)}})-sparse partitions, poly-time
-- statement:
--   There are universal constants $c_1,c_2>0$ such that for every connected $K_r$-minor-free weighted graph $G$ on $n\ge1$ vertices (weights in $[1,n^k]$) and every $\Delta>0$: **(E)** $G$ has a $\Delta$-diameter strong $(\alpha,\tau)$-sparse partition with
--   $$\alpha=(\log_2 n)^{2^{c_1 r\log_2 r}},\qquad \tau=2^{2^{c_2r\log_2r}};$$
--   and **(A)** one admissible program, for all $r,k$ with constants $C,K$, computes such a partition from $(G,\Delta,r)$ in at most $Cn^K+C$ steps on every run.
--
--   Every ball of radius $\Delta/\alpha$ thus meets a number of clusters independent of $n$; the paper notes logarithmic padding is already required for trees, and general graphs need polynomial padding. Theorem 4 turns these partitions into separated neighborhood covers.
--
--   **Formalization Note.** At $n=1$, $\alpha=0$ and Lean's $\Delta/0=0$ makes the ball a single vertex; the statement is then trivial, as it is in the source.
--
--   Differences from the source:
--   - reading: 'computable in polynomial time' → one program of the machine `Program` (SmaleNinth real-RAM core plus `coin` and `roundUpPow`, rational literals), fixed before r and the graph, every run of which halts within C·n^K + C steps with a valid output on every coin tape; reason: the paper names no machine (§9.2, p. 53); 'polynomial time' without 'with high probability' is read as zero-error, the stronger reading
--   - reading: the two O(r log r) exponents → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 16, Theorem 2

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Theorem 2** (Strong Sparse Partition for Minor-Free Graphs, p. 16). There are universal
`c₁, c₂` such that every connected `K_r`-minor-free weighted graph has, for every `∆ > 0`, a
`∆`-diameter strong `((log n)^{2^{c₁ r log r}}, 2^{2^{c₂ r log r}})`-sparse partition, and one
program computes such a partition in `C n^K + C` steps on every run. Weights in `[1, n^k]`
(§3 convention). -/
theorem theorem_2 :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ) (Δ : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 0 < Δ →
        ∃ P : Finset (Finset V), IsStrongSparsePartition G P Δ
          ((Real.logb 2 (Fintype.card V)) ^ ((2 : ℝ) ^ (c₁ * r * Real.logb 2 r)))
          ((2 : ℝ) ^ ((2 : ℝ) ^ (c₂ * r * Real.logb 2 r)))) ∧
      ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ r k : ℕ, ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (Δ : ℝ)
            (E : Encoding G),
            Connected G → MinorFree G r → AspectBounded G k → 0 < Δ →
            ComputesSurely A noOracle (E.cells ++ [Δ, (r : ℝ)])
              (PartitionOut E fun P => IsStrongSparsePartition G P Δ
                ((Real.logb 2 (Fintype.card V)) ^ ((2 : ℝ) ^ (c₁ * r * Real.logb 2 r)))
                ((2 : ℝ) ^ ((2 : ℝ) ^ (c₂ * r * Real.logb 2 r))))
              (C * (Fintype.card V : ℝ) ^ K + C) := by sorry

end MinorFreeSTC.Main
