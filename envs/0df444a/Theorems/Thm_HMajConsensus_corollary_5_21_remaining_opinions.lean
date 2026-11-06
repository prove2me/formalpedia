-- Prove2me | Theorems.Thm_HMajConsensus_corollary_5_21_remaining_opinions
-- name    : HMajConsensus.corollary_5_21_remaining_opinions
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:44.949521+00:00
-- url     : https://prove2.me/theorems/60ae43e0-9812-43e7-9f37-258dfc73d011
-- title:
--   Corollary 5.21 — at most $Cn\log n/T$ opinions survive to round $T$, and $p_{\max}(T)\ge T/(Cn\log n)$, w.h.p.
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Consider $h$-Majority with $h\ge2$ on $n\ge2$ nodes and $2\le k\le n$ opinions, from an arbitrary initial configuration. For every fixed integer $1\le T\le n\log n$, with high probability
--   $$\big|\{i\in[k]:p_i(T)>0\}\big|\ \le\ \frac{Cn\log n}{T},$$
--   and in particular $p_{\max}(T)\ge T/(Cn\log n)$ with high probability.
--
--   The corollary transfers the opinion reduction of Voter to $h$-Majority through the coupling of Theorem 5.14; it is how the proof of Theorem 7.1 handles configurations in which no opinion is initially large.
--
--   **Formalization Note** "With high probability" means probability at least $1-n^{-c}$; the constants $C,c>0$ are fixed before $n,k,h$, the configuration and $T$. Both events are stated with the same $c$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: log n (base not stated), also in the range 1 ≤ T ≤ n log n → Real.log (natural logarithm); reason: the paper computes with the natural log (proof of Lemma 6.9, p.39: exp(−(2A/625) log n) = O(n^{−3}); proof of Lemma 7.2, p.51: 2n exp(−rT) ≤ n^{−20} for T = ⌈C′ log n/r⌉)
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k] → Fin n, Fin k (0-based labels); reason: Lean convention; same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Corollary 5.21, p.28

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Corollary 5.21** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §5.2, p.28): there is an absolute constant `C > 0` such that for
`h`-Majority with `h ≥ 2` on `n ≥ 2` nodes, from an arbitrary initial configuration, for every
fixed integer `1 ≤ T ≤ n log n`, with high probability
`|{i ∈ [k] : p_i(T) > 0}| ≤ C n log n / T`; in particular `pmax(T) ≥ T/(C n log n)` with high
probability.

**Formalization Note** "With high probability" is `≥ 1 − n^{−c}` with `c > 0`; `C` and `c` are
chosen before `n, k, h`, the configuration and `T`. `log` is `Real.log`. `2 ≤ k ≤ n` are the
paper's standing parameters (p.2). -/
theorem corollary_5_21_remaining_opinions :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 2 ≤ h → ∀ (C₀ : Config n k) (T : ℕ), 1 ≤ T →
        (T : ℝ) ≤ n * Real.log n →
        (1 - (n : ℝ) ^ (-c) ≤ (pathLaw h C₀ {ω |
            ((Finset.univ.filter (fun i => 0 < density (ω T) i)).card : ℝ) ≤
              C * n * Real.log n / T}).toReal ∧
          1 - (n : ℝ) ^ (-c) ≤ (pathLaw h C₀ {ω |
            (T : ℝ) / (C * n * Real.log n) ≤ pmax (ω T)}).toReal) := by sorry

end HMajConsensus
