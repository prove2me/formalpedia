-- Prove2me | Theorems.Thm_HMajConsensus_lemma_7_2_unique_strong_opinion
-- name    : HMajConsensus.lemma_7_2_unique_strong_opinion
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:16:34.782851+00:00
-- url     : https://prove2.me/theorems/968f3aa9-1ac2-44fd-a614-a0622f41320d
-- title:
--   Lemma 7.2 — emergence of the unique strong opinion: $\Pr[\exists j\ne I_T: p_j(T)\ge\frac34p_{\max}(T)]\le n^{-10}$
-- statement:
--   Consider $h$-Majority with $h\ge3$ on $n$ nodes and $2\le k\le n$ opinions. Suppose
--   $$p_{\max}(0)\ \ge\ C\max\Big\{\frac{(\log n)^2}{n},\ \frac{\log n}{h\sqrt n}\Big\}$$
--   for a sufficiently large constant $C>0$. Then for some $T=O\big(\log n/\min\{h^2p_{\max}(0),1\}\big)$,
--   $$\Pr\Big[\exists j\ne I_T:\ p_j(T)\ge\frac34p_{\max}(T)\Big]\ \le\ n^{-10},$$
--   where $I_T$ is the smallest index of maximal density at round $T$.
--
--   After this many rounds only one opinion remains within a factor $3/4$ of the maximum, which yields the gap condition of the plurality-consensus result (Theorem 6.1).
--
--   **Formalization Note** $C$ and the $O$ constant $C'$ are chosen before $n,k,h$ and the configuration; a larger $C$ only strengthens the hypothesis, so this is the statement for every sufficiently large $C$. The round $T\in\mathbb N$ may depend on everything and satisfies $T\le C'\log n/\min\{h^2p_{\max}(0),1\}$. $I_T$ is evaluated on the random configuration at round $T$.
--
--   Differences from the source:
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 7.2, p.41 (I_t, p.40)

import Mathlib
import Definitions.Def_HMajConsensus_potential

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 7.2** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §7, p.41): suppose `pmax(0) ≥ C max{(log n)²/n, log n/(h√n)}` for a
sufficiently large constant `C > 0`. Then for some `T = O(log n/min{h²pmax(0), 1})`,
`Pr[∃ j ≠ I_T : p_j(T) ≥ (3/4) pmax(T)] ≤ n^{−10}`.

**Formalization Note** `C` and the `O` constant `C'` are chosen before `n, k, h ≥ 3` and the
configuration (a larger `C` only strengthens the hypothesis); `T ∈ ℕ` may depend on all of them.
`I_T` is evaluated on the random configuration at round `T` (`IsTopIdx`). -/
theorem lemma_7_2_unique_strong_opinion :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ C₀ : Config n k,
        C * max (Real.log n ^ 2 / n) (Real.log n / (h * Real.sqrt n)) ≤ pmax C₀ →
        ∃ T : ℕ, (T : ℝ) ≤ C' * Real.log n / min ((h : ℝ) ^ 2 * pmax C₀) 1 ∧
          (pathLaw h C₀ {ω | ∃ j : Fin k, ¬ IsTopIdx (ω T) j ∧
            (3 / 4) * pmax (ω T) ≤ density (ω T) j}).toReal ≤ (n : ℝ) ^ (-10 : ℝ) := by sorry

end HMajConsensus
