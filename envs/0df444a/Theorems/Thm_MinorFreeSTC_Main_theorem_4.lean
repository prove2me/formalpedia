-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_4
-- name    : MinorFreeSTC.Main.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:20:10.198566+00:00
-- url     : https://prove2.me/theorems/363b421e-3115-49f8-bf3e-de8fdbb0ad8f
-- title:
--   Theorem 4 — strong neighborhood covers of size 2^{2^{O(r log r)}}, padding (log n)^{2^{O(r log r)}}, separation (log n)^{−2^{O(r log r)}}, poly-time w.h.p.
-- statement:
--   There are universal constants $c_1,c_2,c_3>0$ such that for every connected $K_r$-minor-free weighted graph $G$ on $n\ge1$ vertices (weights in $[1,n^k]$) and every $\Delta>0$: **(E)** $G$ admits a strong neighborhood cover of diameter $\Delta$ with
--   $$\text{size}\le\tau=2^{2^{c_1r\log_2r}},\qquad\text{padding }\alpha=(\log_2n)^{2^{c_2r\log_2r}},\qquad\text{separation }s=(\log_2n)^{-2^{c_3r\log_2r}};$$
--   **(A)** for every $c>1$ one admissible program, for all $r,k$ with constants $C,K$, computes such a cover from $(G,\Delta,r)$ in at most $Cn^K+C$ steps on every run, failing on a set of coin tapes of measure at most $n^{-c}$.
--
--   These separated covers feed Theorem 9 and, through Lemma 24, give Theorem 11.
--
--   Differences from the source:
--   - reading: 'computable in polynomial time with high probability' → for every c > 1 one program of the machine `Program` (the published SmaleNinth real-RAM core plus a fair `coin` and `roundUpPow`, rational literals), fixed before r, ϵ and the graph, every run of which halts within C·n^K + C steps (C, K depending only on the parameters named in the statement) and whose failure set of coin tapes has measure ≤ n^{−c}; reason: the paper names no machine; §9.2 (p. 53) lists the assumed operations, and p. 13 defines 'with high probability' as probability ≥ 1 − n^{−c} for a constant c that can be made arbitrarily large
--   - reading: the three O(r log r) exponents → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - reading: 'size τ = 2^{2^{O(r log r)}}' → at most τ partial partitions; reason: 'size' bounds the number of partial partitions; an empty partial partition may pad the count
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 18, Theorem 4

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Theorem 4** (Strong Neighborhood Cover for Minor-Free Graphs with Separation, p. 18). There
are universal `c₁, c₂, c₃` such that every connected `K_r`-minor-free weighted graph has, for every
`∆ > 0`, a strong neighborhood cover of diameter `∆`, size at most `τ = 2^{2^{c₁ r log r}}`,
padding `α = (log n)^{2^{c₂ r log r}}` and separation `s = (log n)^{−2^{c₃ r log r}}`, and for
every `c > 1` one program computes one in `C n^K + C` steps with failure probability at most
`n^{−c}`. -/
theorem theorem_4 :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ) (Δ : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 0 < Δ →
        ∃ (m : ℕ) (𝒞 : Fin m → Finset (Finset V)),
          IsSepCover G m 𝒞 ((2 : ℝ) ^ ((2 : ℝ) ^ (c₁ * r * Real.logb 2 r)))
            ((Real.logb 2 (Fintype.card V)) ^ ((2 : ℝ) ^ (c₂ * r * Real.logb 2 r))) Δ
            ((Real.logb 2 (Fintype.card V)) ^ (-(2 : ℝ) ^ (c₃ * r * Real.logb 2 r)))) ∧
      ∀ c : ℝ, 1 < c → ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ r k : ℕ, ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (Δ : ℝ)
            (E : Encoding G),
            Connected G → MinorFree G r → AspectBounded G k → 0 < Δ →
            ComputesWHP A noOracle (E.cells ++ [Δ, (r : ℝ)])
              (CoverOut E fun m 𝒞 =>
                IsSepCover G m 𝒞 ((2 : ℝ) ^ ((2 : ℝ) ^ (c₁ * r * Real.logb 2 r)))
            ((Real.logb 2 (Fintype.card V)) ^ ((2 : ℝ) ^ (c₂ * r * Real.logb 2 r))) Δ
            ((Real.logb 2 (Fintype.card V)) ^ (-(2 : ℝ) ^ (c₃ * r * Real.logb 2 r))))
              (C * (Fintype.card V : ℝ) ^ K + C) ((Fintype.card V : ℝ) ^ (-c)) := by sorry

end MinorFreeSTC.Main
