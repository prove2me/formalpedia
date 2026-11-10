-- Prove2me | Theorems.Thm_MinSumRadiiPTAS_Main_theorem_1_1
-- name    : MinSumRadiiPTAS.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T22:02:05.521717+00:00
-- url     : https://prove2.me/theorems/3ca68b81-837b-41eb-979f-3ee2bdbb3dda
-- title:
--   Theorem 1.1 — a PTAS for minimum sum of radii: a $(1+\varepsilon)$-approximation in time $N^{2^{C/\varepsilon}}$ with probability $\ge 1 - 1/N$
-- statement:
--   **Theorem 1.1** (p. 2). There are one admissible program $P$ of the randomized distance-oracle real RAM and one absolute constant $C$ such that, for every $\varepsilon \in (0, 1/10)$, every $n$ and $k$ with $1 \le k \le n$ and every metric $d$ on $P = \{0, \dots, n-1\}$ (input: $n, k$, $\varepsilon$, distances by oracle), with $N = \max(n, 2)$ and $T = N^{2^{C/\varepsilon}}$:
--
--   - on every random tape the run has halted after $\lfloor T\rfloor$ steps, with work at most $T$, having written a labelling $\sigma : P \to \{0, \dots, k-1\}$ (a partition of $P$ into at most $k$ clusters); and
--   - the set of tapes on which that labelling satisfies
--   $$\sum_{j} \mathrm{rad}(\sigma^{-1}(j)) \le (1 + \varepsilon)\,\mathrm{opt}, \qquad \mathrm{rad}(C) = \min_{p \in P}\max_{q \in C} d(p, q),$$
--   is measurable and has probability at least $1 - 1/N$ under the tape law.
--
--   Differences from the source:
--   - encoding: point set P with |P| = n, a metric d on P → points Fin n (0-based), d : Fin n → Fin n → ℝ with the published MinSumClust.IsMetric (d(p,p)=0, d ≥ 0, symmetry, triangle inequality, d(p,q) > 0 for p ≠ q); reason: same instances
--   - encoding: a partition of P into at most k clusters, its sum of radii, opt → a labelling σ : Fin n → Fin k (empty classes allowed, rad(∅) = 0), msrCost d σ, msrOpt d k; reason: labellings with empty classes are exactly the partitions into at most k clusters
--   - generalization: a (randomized, polynomial-time) algorithm on an unspecified machine → one MinSumFPT.Admissible program of the published randomized distance-oracle real RAM (unit cost per instruction; no floor, √, log/exp or pointer multiplication; rational literals); inputs in the published initState layout (n, k, ε, δ = 0); reason: the machine has fewer primitives than any standard real RAM, so the statement implies the same statement on a richer machine
--   - reading: an algorithm that is given ε (or: "for any ε") → one program P and one constant C chosen before ε; ε is an input in mem 0; reason: "given any ε" makes ε an input of one algorithm, and the O(·) constants are absolute
--   - reading: time n^{2^{O(1/ε)}} → at most ⌊T⌋₊ steps and work ≤ T with T = N^(2^(C/ε)), N = max(n, 2), C absolute; reason: N = max(n, 2) makes the asymptotic bound an exact bound also at n = 1; increasing the absolute C absorbs fixed overhead for n ≥ 2. Asymptotic notation in the source does not impose a literal one-instruction bound at n = 1
--   - reading: running time of a randomized algorithm → worst case: on every tape ω the run has halted within the time bound with a well-formed output; reason: the paper's running times are deterministic bounds (pp. 23, 38–39); success, not time, is probabilistic
--   - reading: "with high probability" → tapeLaw-probability at least 1 − 1/N, N = max(n, 2), of a measurable event; reason: the textbook 1 − n^{−c} with c = 1; the paper's components fail with probability O(1/n²) and repetition reaches any c
-- source:
--   Fabrizio Grandoni, Anupam Gupta, Jatin Yadav, A PTAS for the Minimum Sum of Radii Problem, manuscript dated November 3, 2026 (STOC 2027 submission), SHA-256 99b43d49…, §1.1, Theorem 1.1, p. 2 (assembly p. 28 and p. 40)

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumRadiiPTAS_Main_Basic
import Definitions.Def_MinSumRadiiPTAS_Main_Machine

open scoped Classical

namespace MinSumRadiiPTAS.Main

/-- **Theorem 1.1** (Grandoni, Gupta, Yadav, STOC 2027 submission, SHA-256 99b43d49…, p. 2): a PTAS
for the minimum sum of radii. One admissible program `P` of the randomized distance-oracle real RAM
and one absolute constant `C` such that, for every `ε ∈ (0, 1/10)`, every `1 ≤ k ≤ n` and every
metric `d` on `Fin n`, with `N = max(n, 2)` and `T = N^(2^(C/ε))`: on every random tape the run
has halted after `⌊T⌋₊` steps, having written a labelling `σ : Fin n → Fin k`, with work `≤ T`; and
with probability at least `1 − 1/N` under the tape law that labelling has MSR cost at most
`(1 + ε) · opt`. -/
theorem theorem_1_1 :
    ∃ P : MinSumFPT.Program, MinSumFPT.Admissible P ∧ ∃ C : ℕ,
      ∀ ε : ℝ, 0 < ε → ε < 1 / 10 →
      ∀ (n k : ℕ) (d : Fin n → Fin n → ℝ), 1 ≤ k → k ≤ n → MinSumClust.IsMetric d →
        let N : ℕ := max n 2
        let T : ℝ := (N : ℝ) ^ ((2 : ℝ) ^ ((C : ℝ) / ε))
        (∀ ω : ℕ → ℝ, ∃ σ : Fin n → Fin k,
            MinSumFPT.OutputsLabelling (MinSumFPT.run P n k ε 0 d ω ⌊T⌋₊) σ ∧
              ((MinSumFPT.run P n k ε 0 d ω ⌊T⌋₊).work : ℝ) ≤ T) ∧
          MeasurableSet (goodTapes P n k ε d T) ∧
          ENNReal.ofReal (1 - 1 / (N : ℝ)) ≤ MinSumFPT.tapeLaw (goodTapes P n k ε d T) := by sorry

end MinSumRadiiPTAS.Main
