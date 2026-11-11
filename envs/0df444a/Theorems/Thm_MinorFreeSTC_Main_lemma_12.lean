-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_lemma_12
-- name    : MinorFreeSTC.Main.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:21:00.271403+00:00
-- url     : https://prove2.me/theorems/5da70aaf-2429-48ea-b5af-f8cb0e88071f
-- title:
--   Lemma 12 — tiled centered neighborhood covers: m(r,ϵ) ≤ O(1/ϵ)^r centered partitions with tiling, radius ≤ 3∆ and (1+ϵ) centered distances on [∆, 2∆], poly-time w.h.p.
-- statement:
--   Let $c_0\ge1$ be a constant of Corollary 1. There are a universal constant $c$ and a count $m(r,\epsilon)\le(c/\epsilon)^r$ depending only on $r$ and $\epsilon$ such that the following holds. Let $G$ be a connected $n$-vertex $K_r$-minor-free weighted graph (weights in $[1,n^k]$), $\Delta>0$, $\epsilon\in(0,1)$, and $\mathcal P$ a partition of $V$ into clusters of strong diameter at most
--   $$\delta\le\frac{\epsilon\Delta}{8c_0r\log_2n}.$$
--   **(E)** There are partitions $\mathcal C_1,\dots,\mathcal C_{m(r,\epsilon)}$ with centers $\mathrm{cent}_i(C)\in C$ such that every cluster is a union of clusters of $\mathcal P$, $\operatorname{rad}(C,\mathrm{cent}_i(C))\le3\Delta$, and every $u,v$ with $\Delta\le d_G(u,v)\le2\Delta$ lie in some $C\in\mathcal C_i$ with $d_C(u,\mathrm{cent}_i(C))+d_C(v,\mathrm{cent}_i(C))\le(1+\epsilon)d_G(u,v)$. **(A)** For every $c'>1$ one admissible program computes such a family from $(G,\Delta,\epsilon,r,\mathcal P)$ in at most $Cn^K+C$ steps, failing with coin-tape measure at most $n^{-c'}$.
--
--   These are the single-scale building blocks of the centered hierarchies of Theorem 9.
--
--   Differences from the source:
--   - reading: 'we can, with high probability, construct in polynomial time' → for every c > 1 one program of the machine `Program` (the published SmaleNinth real-RAM core plus a fair `coin` and `roundUpPow`, rational literals), fixed before r, ϵ and the graph, every run of which halts within C·n^K + C steps (C, K depending only on the parameters named in the statement) and whose failure set of coin tapes has measure ≤ n^{−c}; reason: the paper names no machine; §9.2 (p. 53) lists the assumed operations, and p. 13 defines 'with high probability' as probability ≥ 1 − n^{−c} for a constant c that can be made arbitrarily large
--   - reading: 'where c0 ≥ 1 is a fixed constant' (§7.1: the fixed constant from Corollary 1) → hypotheses 1 ≤ c₀ and `CopConstant c₀` (Corollary 1 holds with c₀); the conclusion for every such c₀; reason: names 'the constant of Corollary 1' without choosing one
--   - reading: 'm ≤ O(1/ϵ)^r depends only on r and ϵ' → a function m : ℕ → ℝ → ℕ with m r ϵ ≤ (c/ϵ)^r, c universal, fixed before the graph; reason: states 'depends only on r and ϵ' literally
--   - encoding: δ ≤ ϵ∆/(8c₀ r log n) → δ·(8c₀·r·log₂ n) ≤ ϵ·∆; reason: avoids division by zero at n = 1
--   - encoding: 'C is a union of clusters of P' → ∃ Q ⊆ P with C = ⋃Q; reason: literal
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), pp. 29–30, Lemma 12

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine
import Definitions.Def_MinorFreeSTC_Main_CopConstant

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Lemma 12** (Tiled Centered Neighborhood Covers, pp. 29–30). Let `c₀ ≥ 1` be a constant of
Corollary 1. There are a universal `c` and a count `m(r, ϵ) ≤ (c/ϵ)^r` depending only on `r` and
`ϵ` such that for every connected `K_r`-minor-free weighted graph, `∆ > 0`, `ϵ ∈ (0, 1)` and
partition `P` into clusters of strong diameter at most `δ ≤ ϵ∆/(8 c₀ r log n)`, there are
`m(r, ϵ)` centered partitions with the Tiling, Bounded Strong Radius and Centered Distance
Preservation properties, and for every `c' > 1` one program computes them in `C n^K + C` steps
with failure probability at most `n^{−c'}`. -/
theorem lemma_12 (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (hcop : CopConstant c₀) :
    ∃ (c : ℝ) (m : ℕ → ℝ → ℕ), 0 < c ∧
      (∀ (r : ℕ) (ϵ : ℝ), 0 < ϵ → ϵ < 1 → (m r ϵ : ℝ) ≤ (c / ϵ) ^ r) ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ)
        (Δ ϵ δ : ℝ) (P : Finset (Finset V)),
        Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → 0 < ϵ → ϵ < 1 →
        IsTiling G P δ → δ * (8 * c₀ * r * Real.logb 2 (Fintype.card V)) ≤ ϵ * Δ →
        ∃ (Cs : Fin (m r ϵ) → Finset (Finset V)) (cent : Fin (m r ϵ) → Finset V → V),
          IsTiledCenteredFamily G P Δ ϵ (m r ϵ) Cs cent) ∧
      ∀ c' : ℝ, 1 < c' → ∃ A : Program, Admissible A ∧ NoOracle A ∧
        ∀ (r k : ℕ) (ϵ : ℝ), 0 < ϵ → ϵ < 1 → ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (Δ δ : ℝ)
            (P : Finset (Finset V)) (L : V → ℝ) (E : Encoding G),
            Connected G → MinorFree G r → AspectBounded G k → 0 < Δ → IsTiling G P δ →
            δ * (8 * c₀ * r * Real.logb 2 (Fintype.card V)) ≤ ϵ * Δ → labelPartition L = P →
            ComputesWHP A noOracle (E.cells ++ [Δ, ϵ, (r : ℝ)] ++ E.labelCells L)
              (CenteredFamilyOut E fun m' Cs cent => ∃ h : m' = m r ϵ,
                IsTiledCenteredFamily G P Δ ϵ (m r ϵ) (fun i => Cs (Fin.cast h.symm i))
                  (fun i => cent (Fin.cast h.symm i)))
              (C * (Fintype.card V : ℝ) ^ K + C) ((Fintype.card V : ℝ) ^ (-c')) := by sorry

end MinorFreeSTC.Main
