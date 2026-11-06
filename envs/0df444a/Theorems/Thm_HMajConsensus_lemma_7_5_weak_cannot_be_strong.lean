-- Prove2me | Theorems.Thm_HMajConsensus_lemma_7_5_weak_cannot_be_strong
-- name    : HMajConsensus.lemma_7_5_weak_cannot_be_strong
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:09.800884+00:00
-- url     : https://prove2.me/theorems/e8b3b103-b5b2-47d4-9d53-48ff4cf3630f
-- title:
--   Lemma 7.5 — a weak opinion stays below $\frac34p_{\max}$: $\Pr[\exists t\le T:p_j(t)\ge\frac34p_{\max}(t)]\le\exp(-\Omega(np_{\max}(0)/T))$
-- statement:
--   Consider $h$-Majority with $h\ge3$ on $n$ nodes and $2\le k\le n$ opinions. There is an absolute constant $c>0$ such that, for every initial configuration and every opinion $j$ with $p_j(0)\le p_{\max}(0)/2$, and for any $T>0$,
--   $$\Pr\Big[\exists t\le T:\ p_j(t)\ge\frac34p_{\max}(t)\Big]\ \le\ \exp\Big(-c\,\frac{np_{\max}(0)}{T}\Big).$$
--
--   Once an opinion is weak, it is unlikely to become strong again within the time horizon of symmetry breaking (proof of Lemma 7.2).
--
--   **Formalization Note** As in Lemma 7.3: $c$ is chosen before $n,k,h$, the configuration, $j$ and $T$; $T$ is a positive real and rounds $t\in\mathbb N$ satisfy $t\le T$.
--
--   Differences from the source:
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 7.5, p.42

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 7.5** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §7.1, p.42): let `j` be an opinion with `p_j(0) ≤ pmax(0)/2`. Then for
any `T > 0`, `Pr[∃ t ≤ T : p_j(t) ≥ (3/4) pmax(t)] ≤ exp(−Ω(n pmax(0)/T))`.

**Formalization Note** As Lemma 7.3: `c > 0` before `n, k, h ≥ 3`, the configuration, `j` and
`T`; real `T`. -/
theorem lemma_7_5_weak_cannot_be_strong :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ (C₀ : Config n k) (j : Fin k),
        density C₀ j ≤ pmax C₀ / 2 → ∀ T : ℝ, 0 < T →
        (pathLaw h C₀ {ω | ∃ t : ℕ, (t : ℝ) ≤ T ∧
            (3 / 4) * pmax (ω t) ≤ density (ω t) j}).toReal ≤
          Real.exp (-(c * (n * pmax C₀ / T))) := by sorry

end HMajConsensus
