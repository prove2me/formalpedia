-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_4
-- name    : MinorFreeSTC.Main.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:20:26.796523+00:00
-- url     : https://prove2.me/theorems/3466f6a4-4b0b-45fc-8b90-7f170cf5d5c7
-- title:
--   Lemma 4 — a ∆-diameter strong (α,τ)-sparse partition yields, in polynomial time, a (3∆/2)-diameter, 6α-padded, 1/(6α)-separated cover of size O(τ r √log r)
-- statement:
--   There is a universal constant $c>0$ such that the following holds. Let $G$ be a connected $K_r$-minor-free weighted graph on $n\ge1$ vertices (weights in $[1,n^k]$), $\Delta>0$, $\alpha,\tau\ge1$, and $\mathcal P$ a $\Delta$-diameter strong $(\alpha,\tau)$-sparse partition of $G$. **(E)** $G$ has a strong neighborhood cover of
--   $$\text{diameter }\tfrac{3\Delta}{2},\quad\text{padding }6\alpha,\quad\text{separation }\tfrac1{6\alpha},\quad\text{size at most } c\,\tau\,r\sqrt{\log_2 r};$$
--   **(A)** one admissible program, for all $r,k$ with constants $C,K$, constructs such a cover from $(G,\Delta,\alpha,\tau,r,\mathcal P)$ in at most $Cn^K+C$ steps on every run.
--
--   With Theorem 2 (at diameter $2\Delta/3$) this gives Theorem 4.
--
--   Differences from the source:
--   - reading: 'we can construct in polynomial time' → one program of the machine `Program` (SmaleNinth real-RAM core plus `coin` and `roundUpPow`, rational literals), fixed before r and the graph, every run of which halts within C·n^K + C steps with a valid output on every coin tape; reason: the paper names no machine (§9.2, p. 53); 'polynomial time' without 'with high probability' is read as zero-error, the stronger reading
--   - reading: O(τ r √log r) → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
--   - encoding: the partition P handed to the algorithm → a vertex labelling L whose fibres are P (`labelPartition L = P`), for every such L; reason: a concrete input layout
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 19, Lemma 4

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 4** (p. 19). There is a universal `c` such that, for every `K_r`-minor-free weighted
graph `G` and every `∆`-diameter strong `(α, τ)`-sparse partition `P` of `G` (`∆ > 0`,
`α, τ ≥ 1`), `G` has a `(3∆/2)`-diameter, `6α`-padded, `1/(6α)`-separated neighborhood cover of
size at most `c τ r √(log r)`, and one program constructs one from `(G, ∆, α, τ, r, P)` in
`C n^K + C` steps on every run. -/
theorem lemma_4 :
    ∃ c : ℝ, 0 < c ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ)
        (P : Finset (Finset V)) (Δ α τ : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → 1 ≤ α → 1 ≤ τ →
        IsStrongSparsePartition G P Δ α τ →
        ∃ (m : ℕ) (𝒞 : Fin m → Finset (Finset V)),
          IsSepCover G m 𝒞 (c * τ * r * Real.sqrt (Real.logb 2 r)) (6 * α) (3 * Δ / 2) (1 / (6 * α))) ∧
      ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ r k : ℕ, ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V)
            (P : Finset (Finset V)) (Δ α τ : ℝ) (L : V → ℝ) (E : Encoding G),
            Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → 1 ≤ α → 1 ≤ τ →
            IsStrongSparsePartition G P Δ α τ → labelPartition L = P →
            ComputesSurely A noOracle (E.cells ++ [Δ, α, τ, (r : ℝ)] ++ E.labelCells L)
              (CoverOut E fun m 𝒞 =>
                IsSepCover G m 𝒞 (c * τ * r * Real.sqrt (Real.logb 2 r)) (6 * α) (3 * Δ / 2) (1 / (6 * α)))
              (C * (Fintype.card V : ℝ) ^ K + C) := by sorry

end MinorFreeSTC.Main
