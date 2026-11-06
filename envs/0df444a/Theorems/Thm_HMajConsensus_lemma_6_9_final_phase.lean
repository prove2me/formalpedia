-- Prove2me | Theorems.Thm_HMajConsensus_lemma_6_9_final_phase
-- name    : HMajConsensus.lemma_6_9_final_phase
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:50.165191+00:00
-- url     : https://prove2.me/theorems/905fd1a8-c3f5-472b-92fc-ff7fa60a14a6
-- title:
--   Lemma 6.9 — from $p_1(0)\ge3/5$, consensus on opinion 1 in $O(\log n)$ rounds w.p. $\ge1-1/n^2$ (corrected: for $n\ge n_0$)
-- statement:
--   Consider $h$-Majority with $h\ge3$ on $n$ nodes and $2\le k\le n$ opinions, and let $i_0$ be an opinion with $p_{i_0}(0)\ge3/5$. There are absolute constants $C'>0$ and $n_0$ such that for all $n\ge n_0$, the process reaches consensus on opinion $i_0$ within $C'\log n$ rounds with probability at least
--   $$1-\frac1{n^2}.$$
--
--   This is the final phase of the plurality-consensus argument (§6.3): once the plurality opinion holds a $3/5$ fraction, it takes over in logarithmic time.
--
--   **Formalization Note** "Reaches consensus on opinion $i_0$ within $C'\log n$ rounds" is: some round $t\in\mathbb N$ with $t\le C'\log n$ has every node holding $i_0$. The constants are chosen before $n,k,h$ and the configuration. The threshold $n_0$ corrects the printed statement, which is false for small $n$ (see below).
--
--   Differences from the source:
--   - correction: the statement for every n ("with probability at least 1 − 1/n²", no threshold) → ∃ C′ > 0, ∃ n₀, ∀ n ≥ n₀; reason: false as printed: n = 5, k = 2, h = 3, three nodes on opinion 1 (p₁(0) = 3/5, every assumption holds); the opinion-1 count is the chain m ↦ Binomial(5, q(m/5)), q(p) = p³ + 3p²(1 − p), which is absorbed at the all-opinion-1 state with probability ≈ 0.7045 < 1 − 1/25 in any number of rounds; the proof (p.39) is asymptotic (sufficiently large A, B)
--   - encoding: opinion 1 of §6 (other opinions not sorted, p.28; p₁(0) ≥ 3/5 makes it the unique majority) → a label i₀ : Fin k with density ≥ 3/5; reason: §6 fixes only which opinion is opinion 1; same instances
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 6.9, p.39

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 6.9** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §6.3, p.39), corrected: if `p₁(0) ≥ 3/5`, then the process reaches
consensus on opinion 1 in `O(log n)` rounds with probability at least `1 − 1/n²` — **for all
`n ≥ n₀`**.

**Formalization Note** The printed statement is false for small `n` (counterexample `n = 5`,
`k = 2`, `h = 3`, three nodes on opinion 1: consensus on opinion 1 ever happens with probability
`≈ 0.7045 < 1 − 1/25`); the minimal correction adds a threshold `n₀`, chosen with the `O`
constant before `n, k, h` and the configuration. -/
theorem lemma_6_9_final_phase :
    ∃ C' : ℝ, 0 < C' ∧ ∃ n₀ : ℕ, ∀ (n k h : ℕ), n₀ ≤ n → 2 ≤ k → k ≤ n → 3 ≤ h →
      ∀ (C₀ : Config n k) (i₀ : Fin k), 3 / 5 ≤ density C₀ i₀ →
        1 - 1 / (n : ℝ) ^ 2 ≤ (pathLaw h C₀ {ω | ∃ t : ℕ,
          (t : ℝ) ≤ C' * Real.log n ∧ ∀ v, ω t v = i₀}).toReal := by sorry

end HMajConsensus
