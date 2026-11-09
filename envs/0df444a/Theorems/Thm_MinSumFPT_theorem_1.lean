-- Prove2me | Theorems.Thm_MinSumFPT_theorem_1
-- name    : MinSumFPT.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:17:13.383296+00:00
-- url     : https://prove2.me/theorems/ff18392e-efa4-41e8-8a13-8b1ac6640e40
-- title:
--   Theorem 1 — $(1+\varepsilon)$-approximate $k$-minsum clustering in $n^{1+o(1)}2^{2^{O(k\log(k/\varepsilon))}}$ time
-- statement:
--   Let $A$ be a set of $n\ge1$ points with a semi-metric $d$ (non-negative, symmetric, triangle inequality, $d(x,x)=0$, distinct points may be at distance $0$), and let $k\ge1$ and $\varepsilon\in(0,1)$. Write $\mathrm{OPT}_k(d)$ for the optimal k-minsum cost $\min\sum_i\sum_{x,y\in C_i}d(x,y)$ over clusterings into $k$ clusters.
--
--   For every failure probability $\delta\in(0,1)$ there is a single randomized algorithm (a program of the distance-oracle real RAM, reading $n$, $k$ and $\varepsilon$, with each distance query costing one operation), together with a constant $C$ and a function $g(n)\to0$, both independent of $n,k,\varepsilon$, such that for every input:
--
--   1. on every random tape the algorithm halts within
--   $$
--   n^{1+g(n)}\cdot2^{2^{C\,k\log_2(k/\varepsilon)}}
--   $$
--   steps and outputs a clustering of $A$ into $k$ clusters (all nonempty when $k\le n$);
--   2. with probability at least $1-\delta$ the output satisfies
--   $$
--   \mathrm{cost}(\text{output})\ \le\ (1+\varepsilon)\cdot\mathrm{OPT}_k(d).
--   $$
--
--   Since an explicit semi-metric has $\Theta(n^2)$ entries, this is a sublinear-time approximation scheme for k-minsum clustering, fixed-parameter in $k$.
--
--   **Formalization Note** The program runs on `MinSumFPT.Machine`. The clustering is a labelling $\sigma:\{0,\dots,n-1\}\to\{0,\dots,k-1\}$ written at the integer addresses $-1-v$. The failure event is the set of tapes on which the halted output costs more than $(1+\varepsilon)\mathrm{OPT}_k(d)$; it has outer measure at most $\delta$ under the law of independent uniform $[0,1]$ tape reals.
--
--   Differences from the source:
--   - reading: "computes" with a randomized algorithm (the proof fixes a failure probability δ ∈ (0,1), p.12) → for every δ ∈ (0,1) one program; time bound on every tape; failure set of outer measure ≤ δ; reason: the strongest of the readings the page supports; implies the constant-probability reading
--   - reading: n^{1+o(1)} · 2^{2^{O(k log(k/ε))}} → n^{1+g(n)} · 2^{2^{C·k·log₂(k/ε)}} with one g → 0 and one C, both uniform in n, k, ε; reason: the proof's n^{o(1)} factors split into n^{o(1)} times a function of k and ε (fixed parameter tractability, footnote 2)
--   - reading: ε, k unspecified ranges → n ≥ 1, k ≥ 1, 0 < ε < 1; reason: the paper works with ε < 1 (Lemma 10, Theorem 8); for ε ≥ k the bound 2^{2^{O(k log(k/ε))}} ≤ 2 is unsupported; k ≥ 1 excludes only the empty problem
--   - reading: a semi-metric: non-negative, symmetric, triangle inequality, co-located points at distance 0 (footnote 1) → MinSumClust.IsPseudometric (adds d(x,x) = 0); reason: a point is co-located with itself; the W₁ embedding (p.8) needs ‖e_x − e_x‖ = 0 = d(x,x)
--   - encoding: a clustering 𝒞 = {C₁ ⊔ ⋯ ⊔ C_k} of A → a labelling σ : Fin n → Fin k, surjective when k ≤ n; OPT the minimum over all labellings; reason: the minimum over labellings equals the minimum over partitions into k nonempty clusters (proved in the sanity file)
--   - encoding: arithmetic operations, d(x,y) a single operation → steps of MinSumFPT.Machine, every instruction one unit, d read only through dist; reason: the page names no machine; no floor, log, exp or sqrt, so the bound is at least as strong
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 1, p.1

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_labCost
open Filter Topology

namespace MinSumFPT

/-- Theorem 1 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 1, p.1): there is an algorithm that on every input `(A, d)` computes a
`(1 + ε)`-approximately optimal k-minsum clustering of `A` using
`n^{1+o(1)} ⋅ 2^{2^{O(k log(k/ε))}}` arithmetic operations, assuming that computing `d(x, y)` is a
single operation.

**Formalization Note.** For every failure probability `δ ∈ (0, 1)` there are one program `P` of
`MinSumFPT.Machine` (inputs `imem 0 = n`, `imem 1 = k`, `mem 0 = ε`; `mem 1 = 0`), a constant
`C` and a function `g → 0`, both uniform in `n, k, ε`, such that for all `n, k ≥ 1`, `ε ∈ (0, 1)`
and every pseudometric `d` on `n` points: on **every** tape `P` halts within
`n^{1+g(n)} ⋅ 2^{2^{C ⋅ k ⋅ log₂(k/ε)}}` steps with a labelling `σ : Fin n → Fin k` written at
`imem (−1 − v)` (using every label when `k ≤ n`), and the tapes on which
`cost(σ) > (1 + ε) ⋅ OPT_k(d)` have outer measure at most `δ` under `tapeLaw`. -/
theorem theorem_1 (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (g : ℕ → ℝ), Tendsto g atTop (𝓝 0) ∧
      ∀ (n k : ℕ) (ε : ℝ) (d : Fin n → Fin n → ℝ), 1 ≤ n → 1 ≤ k → 0 < ε → ε < 1 →
        MinSumClust.IsPseudometric d →
        (∀ ω : ℕ → ℝ, ∃ (t : ℕ) (σ : Fin n → Fin k), OutputsLabelling (run P n k ε 0 d ω t) σ ∧
          ((run P n k ε 0 d ω t).work : ℝ) ≤
            (n : ℝ) ^ (1 + g n) * (2 : ℝ) ^ ((2 : ℝ) ^ (C * k * Real.logb 2 (k / ε))) ∧
          (k ≤ n → Function.Surjective σ)) ∧
        tapeLaw {ω | ∃ (t : ℕ) (σ : Fin n → Fin k), OutputsLabelling (run P n k ε 0 d ω t) σ ∧
            (1 + ε) * optCost d k < labCost d σ} ≤ ENNReal.ofReal δ := by sorry

end MinSumFPT
