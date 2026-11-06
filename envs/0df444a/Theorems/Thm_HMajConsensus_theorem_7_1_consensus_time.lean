-- Prove2me | Theorems.Thm_HMajConsensus_theorem_7_1_consensus_time
-- name    : HMajConsensus.theorem_7_1_consensus_time
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:59.370052+00:00
-- url     : https://prove2.me/theorems/09ee0a9d-51df-4333-aa3f-92d04aff3de7
-- title:
--   Theorem 7.1 — $\tau_{\mathrm{consensus}}\le C\log n/\min\{h^2p_{\max}(0),1\}$ above the threshold, and $\le C(\log n+\sqrt n/h)(\log n)^2$ always, w.h.p.
-- statement:
--   Consider $h$-Majority with $h\ge3$ on $n$ nodes and $2\le k\le n$ opinions. Let $C>0$ be a sufficiently large constant. The following bounds hold with high probability:
--   $$\tau_{\mathrm{consensus}}\ \le\ \begin{cases}\dfrac{C\log n}{\min\{h^2p_{\max}(0),1\}} & \text{if } p_{\max}(0)\ge C\max\Big\{\dfrac{(\log n)^2}{n},\dfrac{\log n}{h\sqrt n}\Big\},\\[2ex] C\Big(\log n+\dfrac{\sqrt n}{h}\Big)(\log n)^2 & \text{for any initial configuration.}\end{cases}$$
--
--   This is the exact form, with logarithmic factors, of the consensus-time bound of Theorem 1.1.
--
--   **Formalization Note** One constant $C$ and one exponent $c$ ("with high probability" $=\ge1-n^{-c}$) serve both clauses and are chosen before $n,k,h$ and the configuration. A larger $C$ strengthens the hypothesis of the first clause and weakens both bounds, so the existence of one $C$ is the statement for every sufficiently large $C$.
--
--   Differences from the source:
--   - encoding: τ_consensus ≤ x (first round at which all nodes agree) → ConsensusBy x: some round t ∈ ℕ with (t : ℝ) ≤ x is a consensus configuration; reason: same event (first hitting time ≤ x); avoids sInf ∅ = 0
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 7.1, p.40

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Theorem 7.1** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §7, p.40): let `C > 0` be a sufficiently large constant. With high
probability, `τ_consensus ≤ C log n / min{h²pmax(0), 1}` if
`pmax(0) ≥ C max{(log n)²/n, log n/(h√n)}`, and `τ_consensus ≤ C (log n + √n/h)(log n)²` for any
initial configuration.

**Formalization Note** One `C` and one w.h.p. exponent `c > 0`, chosen before `n, k, h ≥ 3` and
the configuration; a larger `C` strengthens the hypothesis and weakens the bound, so "some `C`"
is "every sufficiently large `C`". `τ_consensus ≤ x` is `ConsensusBy x`. -/
theorem theorem_7_1_consensus_time :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ C₀ : Config n k,
        (C * max (Real.log n ^ 2 / n) (Real.log n / (h * Real.sqrt n)) ≤ pmax C₀ →
          1 - (n : ℝ) ^ (-c) ≤ (pathLaw h C₀ {ω |
            ConsensusBy (C * Real.log n / min ((h : ℝ) ^ 2 * pmax C₀) 1) ω}).toReal) ∧
        1 - (n : ℝ) ^ (-c) ≤ (pathLaw h C₀ {ω |
          ConsensusBy (C * (Real.log n + Real.sqrt n / h) * Real.log n ^ 2) ω}).toReal := by sorry

end HMajConsensus
