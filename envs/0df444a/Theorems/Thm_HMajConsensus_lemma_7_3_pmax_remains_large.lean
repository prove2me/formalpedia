-- Prove2me | Theorems.Thm_HMajConsensus_lemma_7_3_pmax_remains_large
-- name    : HMajConsensus.lemma_7_3_pmax_remains_large
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:48.300541+00:00
-- url     : https://prove2.me/theorems/ffb9c17c-27f9-4f91-a8d7-60145a24964c
-- title:
--   Lemma 7.3 — $\Pr[\exists t\le T: p_{\max}(t)\le p_{\max}(0)/2]\le\exp(-\Omega(np_{\max}(0)/T))$
-- statement:
--   Consider $h$-Majority with $h\ge3$ on $n$ nodes and $2\le k\le n$ opinions, from any initial configuration. There is an absolute constant $c>0$ such that for any $T>0$,
--   $$\Pr\Big[\exists t\le T:\ p_{\max}(t)\le\frac{p_{\max}(0)}{2}\Big]\ \le\ \exp\Big(-c\,\frac{np_{\max}(0)}{T}\Big).$$
--
--   The maximum density does not collapse over $T$ rounds; this keeps the growth rate $\min\{h^2p_{\max}(t),1\}$ comparable to its initial value during symmetry breaking (proof of Lemma 7.2).
--
--   **Formalization Note** $\Omega$ is the absolute constant $c$, chosen before $n,k,h$, the configuration and $T$. $T$ is a positive real number and the rounds $t$ are natural numbers with $t\le T$.
--
--   Differences from the source:
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Lemma 7.3, p.41

import Mathlib
import Definitions.Def_HMajConsensus_pathLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Lemma 7.3** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §7, p.41): for any `T > 0`,
`Pr[∃ t ≤ T : pmax(t) ≤ pmax(0)/2] ≤ exp(−Ω(n pmax(0)/T))`.

**Formalization Note** `Ω` is an absolute constant `c > 0` chosen before `n, k, h ≥ 3`, the
configuration and `T`; `T` is real and rounds `t ∈ ℕ` are compared after casting. -/
theorem lemma_7_3_pmax_remains_large :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ (C₀ : Config n k) (T : ℝ), 0 < T →
        (pathLaw h C₀ {ω | ∃ t : ℕ, (t : ℝ) ≤ T ∧ pmax (ω t) ≤ pmax C₀ / 2}).toReal ≤
          Real.exp (-(c * (n * pmax C₀ / T))) := by sorry

end HMajConsensus
