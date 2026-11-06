-- Prove2me | Theorems.Thm_HMajConsensus_theorem_1_1_consensus_time
-- name    : HMajConsensus.theorem_1_1_consensus_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:57.974694+00:00
-- url     : https://prove2.me/theorems/fa5158a7-8532-4f04-9154-298084340d29
-- title:
--   Theorem 1.1 — $h$-Majority reaches consensus within $\widetilde O(1+\min\{1/\min\{h^2p_{\max},1\},\sqrt n/h\})$ rounds w.h.p.
-- statement:
--   Consider $h$-Majority on $n$ nodes with $2\le k\le n$ opinions and any sample size $h\ge3$: in each round every node samples $h$ nodes uniformly at random with replacement and adopts the most frequent opinion in its sample, breaking ties uniformly at random. Let $p_{\max}$ be the largest initial opinion density. There are absolute constants $C>0$ and $c>0$ such that, for every $n,k,h$ and every initial configuration, with probability at least $1-n^{-c}$,
--   $$\tau_{\mathrm{consensus}}\ \le\ C(\log n)^3\Big(1+\min\Big\{\frac{1}{\min\{h^2p_{\max},1\}},\ \frac{\sqrt n}{h}\Big\}\Big).$$
--   That is, $h$-Majority reaches consensus within $\widetilde O\big(1+\min\{1/\min\{h^2p_{\max},1\},\sqrt n/h\}\big)$ rounds with high probability.
--
--   This is the paper's main upper bound: the first consensus-time bound for $h$-Majority valid for every sample size $h\ge3$, every number of opinions and every initial configuration. Together with the lower bound of Theorem 1.3 it shows that $h$-Majority is optimal up to polylogarithmic factors among neutral $h$-input dynamics.
--
--   **Formalization Note** $\widetilde O$ hides factors polynomial in $\log n$ (p.2); the statement fixes the factor $(\log n)^3$ that the proof of Theorem 1.1 (p.53) gives. $\log$ is the natural logarithm, $p_{\max}$ the initial maximum density, and $\tau_{\mathrm{consensus}}\le x$ the event that some round $t\in\mathbb N$ with $t\le x$ is a consensus configuration.
--
--   Differences from the source:
--   - reading: Õ(f), "hide factors polynomial in log n" (p.2) → C · (log n)³ · f with an absolute constant C; reason: the proof of Theorem 1.1 (p.53) gives exactly the factor (log n)³; a fixed polynomial factor implies the Õ form, so this is the stronger reading
--   - encoding: τ_consensus ≤ x (first round at which all nodes agree) → ConsensusBy x: some round t ∈ ℕ with (t : ℝ) ≤ x is a consensus configuration; reason: same event (first hitting time ≤ x); avoids sInf ∅ = 0
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 1.1, p.2 (proof: p.53; conventions: p.2)

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Theorem 1.1** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §1.2.1, p.2): for every initial configuration, `h`-Majority reaches
consensus within `Õ(1 + min{1/min{h²pmax, 1}, √n/h})` rounds with high probability.

**Formalization Note** `Õ` is read as the explicit factor `C (log n)³` that the proof of
Theorem 1.1 (p.53) gives; `C` and the w.h.p. exponent `c > 0` are chosen before every
`2 ≤ k ≤ n`, every `h ≥ 3` and every initial configuration. `pmax` is the initial maximum
density; `τ_consensus ≤ x` is `ConsensusBy x`; `log` is `Real.log`. -/
theorem theorem_1_1_consensus_time :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ C₀ : Config n k,
        1 - (n : ℝ) ^ (-c) ≤ (pathLaw h C₀ {ω |
          ConsensusBy (C * Real.log n ^ 3 *
            (1 + min (1 / min ((h : ℝ) ^ 2 * pmax C₀) 1) (Real.sqrt n / h))) ω}).toReal := by sorry

end HMajConsensus
