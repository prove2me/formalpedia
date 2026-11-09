-- Prove2me | Theorems.Thm_MinSumFPT_theorem_5
-- name    : MinSumFPT.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:23.930508+00:00
-- url     : https://prove2.me/theorems/dd692ac9-0ed0-491a-bf00-aff81b2538c0
-- title:
--   Theorem 5 (corrected: $\varepsilon,\delta\in(0,1)$, sets of $\le\eta(k^2/\varepsilon)\log_2(2k/\delta)$ points) — center approximation
-- statement:
--   There are absolute constants $\alpha,\eta>0$ and a single randomized program, taking $n,k,\varepsilon,\delta$ as input, with the following properties. For all $n,k\ge1$, all $\varepsilon,\delta\in(0,1)$ and every pseudometric $d$ on $n$ points:
--
--   1. on every random tape it halts within $\big(n^{1+o(1)}+2^{O(k\log k)}\big)\cdot\big((k/\varepsilon)\cdot\log(1/\delta)\big)^{O(1)}$ steps;
--   2. it outputs a collection of at most $(n/\varepsilon)^{o(1)}+2^{O(k\log k)}$ point sets, each of at most $\eta\cdot(k^2/\varepsilon)\cdot\log_2(2k/\delta)$ points;
--   3. for any partition $\sigma$ of $A$ into $k$ clusters, with probability at least $1-\delta$ one of the output sets $(\varepsilon,\alpha)$-covers every cluster of $\sigma$. Here the $\mathrm{OPT}$ of (1) is the optimal $k$-minsum cost of the instance, for every partition $\sigma$ (footnote 10).
--
--   This is Stage 1 of the algorithm. Among the polylogarithmically many candidate sets, one contains an approximate center for every cluster of the optimal clustering, and also for every cluster of the near-optimal clustering used in Stage 3.
--
--   **Formalization Note** The program runs on `MinSumFPT.Machine`. The bounds hold on every tape, with one function $g\to0$ for both $o(1)$'s and one constant $C$ for all $O(\cdot)$'s, uniform in $n,k,\varepsilon,\delta$; $\log(1/\delta)$ is read as $\log_2(2+1/\delta)$. The failure event has outer measure at most $\delta$ under the tape law.
--
--   Differences from the source:
--   - correction: for every δ, ε > 0; sets of at most η·(k²/ε)·log(k/δ) points → ε, δ ∈ (0,1); sets of at most η·(k²/ε)·log₂(2k/δ) points; reason: false as printed: (i) n = k points at mutual distance 1, σ the singletons, OPT = 0 = cost(σ): every covering set contains all k points, more than η(k²/ε)log(k/δ) once ε > ηk·log(k/δ); (ii) n = k = 1 needs one point while η(1/ε)log(1/δ) < 1 for δ near 1; the proof's sets have k + 1200(k²/ε)ln(k/δ) points (p.18)
--   - generalization: ∃ absolute α, η > 0; for every δ, ε there is an algorithm → ∃ absolute α, η > 0; one program reading ε and δ as inputs; reason: one program for all inputs implies one per (ε, δ)
--   - reading: n^{1+o(1)}, 2^{O(k log k)}, ((k/ε)·log(1/δ))^{O(1)}, (n/ε)^{o(1)} → ∃ g → 0 and ∃ C uniform in n, k, ε, δ, with log(1/δ) read as log₂(2 + 1/δ); reason: decision on O-notation: one constant per O, log ≥ 1 so the bound cannot vanish as δ → 1
--   - reading: a randomized algorithm with the stated time → the time bound on every tape; failure set of outer measure ≤ δ under the uniform tape law; reason: worst-case reading of the time bound; outer measure needs no measurability side condition
--   - encoding: arithmetic operations, d(x,y) a single operation → steps of MinSumFPT.Machine, every instruction one unit, d read only through dist; reason: the page names no machine; no floor, log, exp or sqrt, so the bound is at least as strong
--   - encoding: a partition of A into k clusters → every labelling σ : Fin n → Fin k (empty clusters allowed); reason: an empty cluster is covered by every set, so nothing changes
--   - generalization: (A, d) a finite metric space (§2.1, p.7) → every pseudometric d (d(x,x) = 0, d ≥ 0, symmetric, triangle inequality); reason: the goal's input is a semi-metric (footnote 1, p.1); every metric is a pseudometric
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 5, p.9 (ε, δ range and set-size bound corrected)

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_labCost
import Definitions.Def_MinSumFPT_IsCovered
open Filter Topology

namespace MinSumFPT

/-- Theorem 5 (corrected: ε, δ ∈ (0, 1) and sets of at most η(k²/ε) log₂(2k/δ) points)
(Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 5, p.9): there are absolute constants `α, η > 0` and one randomized
program (inputs `n, k, ε, δ`) running in `(n^{1+o(1)} + 2^{O(k log k)}) ⋅ ((k/ε) ⋅ log(1/δ))^{O(1)}`
steps that outputs at most `(n/ε)^{o(1)} + 2^{O(k log k)}` sets, each of at most
`η ⋅ (k²/ε) ⋅ log(2k/δ)` points, such that for any partition `σ` of `A` into `k` clusters, with
probability at least `1 − δ` one of these sets (ε, α)-covers all clusters of `σ`.

**Formalization Note.** The machine is `MinSumFPT.Machine` (inputs `imem 0 = n`, `imem 1 = k`,
`mem 0 = ε`, `mem 1 = δ`; output sets read by `outputSets`). The time and size bounds hold on
every tape; `o(1)` is one function `g → 0` and `O(·)` one constant `C`, uniform in `n, k, ε, δ`;
`log x` in the time bound is read `log₂(2 + x)`. The failure set (tapes whose output contains no
set covering every cluster of `σ`) has outer measure at most `δ` under `tapeLaw`. In (1) the OPT
of the covering condition is `optCost d k`, the optimum of the instance (§2.2, p.8: "the optimal
k-minsum cost OPT"), for every partition `σ` (footnote 10: "stated with respect to any
clustering"). -/
theorem theorem_5 :
    ∃ α η : ℝ, 0 < α ∧ 0 < η ∧ ∃ P : Program, Admissible P ∧ ∃ (C : ℝ) (g : ℝ → ℝ),
      Tendsto g atTop (𝓝 0) ∧
      ∀ (n k : ℕ) (ε δ : ℝ) (d : Fin n → Fin n → ℝ), 1 ≤ n → 1 ≤ k → 0 < ε → ε < 1 →
        0 < δ → δ < 1 → MinSumClust.IsPseudometric d →
        (∀ ω : ℕ → ℝ, ∃ t, ValidSets n (run P n k ε δ d ω t) ∧
          ((run P n k ε δ d ω t).work : ℝ) ≤
            ((n : ℝ) ^ (1 + g n) + (2 : ℝ) ^ (C * k * Real.logb 2 k)) *
              ((k / ε) * Real.logb 2 (2 + 1 / δ)) ^ C ∧
          ((outputSets (run P n k ε δ d ω t)).length : ℝ) ≤
            ((n : ℝ) / ε) ^ g ((n : ℝ) / ε) + (2 : ℝ) ^ (C * k * Real.logb 2 k) ∧
          ∀ l ∈ outputSets (run P n k ε δ d ω t),
            (l.length : ℝ) ≤ η * ((k : ℝ) ^ 2 / ε) * Real.logb 2 (2 * k / δ)) ∧
        ∀ σ : Fin n → Fin k,
          tapeLaw {ω | ∃ t, ValidSets n (run P n k ε δ d ω t) ∧
            ¬ ∃ l ∈ outputSets (run P n k ε δ d ω t), ∀ i : Fin k,
              IsCovered d (optCost d k) k ε α (toPointSet n l) (clusterOf σ i)} ≤
            ENNReal.ofReal δ := by sorry

end MinSumFPT
