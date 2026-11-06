-- Prove2me | Theorems.Thm_HMajConsensus_theorem_1_2_plurality_consensus
-- name    : HMajConsensus.theorem_1_2_plurality_consensus
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:52.693306+00:00
-- url     : https://prove2.me/theorems/2303b3b8-d773-46c7-8f83-e22ef11985ae
-- title:
--   Theorem 1.2 — plurality consensus within $O(\log n/\min\{h^2p_{\max},1\})$ rounds under a gap $c\sqrt{p_{\max}/\min\{h^2p_{\max},1\}\cdot\log n/n}$
-- statement:
--   Let $h\ge3$ and $2\le k\le n$. There exists an absolute constant $c>0$ such that, for every initial configuration and opinion $i_0$ satisfying
--   $$p_{\max}-p_i\ \ge\ c\sqrt{\frac{p_{\max}}{\min\{h^2p_{\max},1\}}\cdot\frac{\log n}{n}}\qquad\text{for all } i\ne i_0,$$
--   $h$-Majority reaches consensus on opinion $i_0$ within $O\big(\log n/\min\{h^2p_{\max},1\}\big)$ rounds with high probability. Here $p_i$ and $p_{\max}$ are the initial densities.
--
--   The gap required for plurality consensus shrinks as the sample size grows; for $h=3$ it is of order $\sqrt{\log n/n}$.
--
--   **Formalization Note** The $O$ constant $C'$ and the exponent $c'$ of "with high probability" ($\ge1-n^{-c'}$) are chosen with $c$, before $n,k,h$, the configuration and $i_0$. Since the right-hand side is positive for $n\ge2$, the gap hypothesis forces $i_0$ to be the unique opinion of maximal density.
--
--   Differences from the source:
--   - generalization: opinion 1 under the sorting p₁ ≥ ··· ≥ p_k (p.2), gap for all i ≥ 2 → any label i₀, gap for all i ≠ i₀, no sorting of the other opinions; reason: the sorted configuration is the case i₀ = the first label; the gap forces i₀ to be the unique maximizer
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 1.2, p.3

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Theorem 1.2** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §1.2.2, p.3): there is an absolute constant `c > 0` such that, for
every initial configuration with `pmax − p_i ≥ c √(pmax/min{h²pmax, 1} · log n/n)` for all
`i ≥ 2`, `h`-Majority reaches consensus on opinion 1 within `O(log n/min{h²pmax, 1})` rounds with
high probability.

**Formalization Note** "Opinion 1" (the plurality opinion under the p.2 sorting) is any label
`i₀`, with the gap required for every `i ≠ i₀` (this forces `i₀` to be the unique maximizer).
`c`, the `O` constant `C'` and the w.h.p. exponent `c'` are chosen before `n, k, h ≥ 3` and the
configuration. `log` is `Real.log`. -/
theorem theorem_1_2_plurality_consensus :
    ∃ c : ℝ, 0 < c ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ c' : ℝ, 0 < c' ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ (C₀ : Config n k) (i₀ : Fin k),
        (∀ i : Fin k, i ≠ i₀ →
          c * Real.sqrt (pmax C₀ / min ((h : ℝ) ^ 2 * pmax C₀) 1 * (Real.log n / n)) ≤
            pmax C₀ - density C₀ i) →
        1 - (n : ℝ) ^ (-c') ≤ (pathLaw h C₀ {ω | ∃ t : ℕ,
          (t : ℝ) ≤ C' * Real.log n / min ((h : ℝ) ^ 2 * pmax C₀) 1 ∧
            ∀ v, ω t v = i₀}).toReal := by sorry

end HMajConsensus
