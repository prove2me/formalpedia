-- Prove2me | Theorems.Thm_HMajConsensus_corollary_5_12_winner_order
-- name    : HMajConsensus.corollary_5_12_winner_order
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:13:48.607885+00:00
-- url     : https://prove2.me/theorems/c8ad81f1-939c-4a26-bc53-981a4a8aaa35
-- title:
--   Corollary 5.12 — $\Pr[W_i]\le(p_i/p_1)\Pr[W_1]\le\Pr[W_1]$ and $\Pr[W_1]\ge p_1$
-- statement:
--   Let $p$ be a probability vector on $[k]$, $h\ge3$, $X\sim\mathrm{Multinomial}(h;p)$ and $W_i=\{\mathrm{Maj}(X)=i\}$ with uniform tie-breaking. Suppose $p_1=\max_{i\in[k]}p_i$. Then for every $i\in[k]$,
--   $$\Pr[W_i]\ \le\ \frac{p_i}{p_1}\Pr[W_1]\ \le\ \Pr[W_1],$$
--   and in particular $\Pr[W_1]\ge p_1$.
--
--   The corollary says that one round of $h$-Majority never lets another opinion overtake the plurality opinion in expectation, and that the expected density of the plurality opinion does not decrease; §6 uses it as $\eta(t)\ge1$.
--
--   **Formalization Note** $\Pr[W_i]$ is `winProb h p i`; "opinion 1" is any label $i_1$ with $p_{i_1}=\max_jp_j$. $h\ge3$ is the paper's standing sample size (Theorem 5.1).
--
--   Differences from the source:
--   - generalization: p = p(t), the current empirical distribution (§5, p.14) → every probability vector p : PMF (Fin k), opinion 1 any label i₁ with p_{i₁} = max_j p_j; reason: p(t) is a probability vector; the corollary itself only assumes p₁ = max_i p_i
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Corollary 5.12, p.24

import Mathlib
import Definitions.Def_HMajConsensus_majLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Corollary 5.12** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §5.1.5, p.24): suppose `p₁ = max_{i ∈ [k]} p_i`. Then for every
`i ∈ [k]`, `Pr[W_i] ≤ (p_i/p₁) Pr[W₁] ≤ Pr[W₁]`; in particular `Pr[W₁] ≥ p₁`.

**Formalization Note** `h ≥ 3` is the standing sample size of §5 (Theorem 5.1). "Opinion 1" is
any label `i₁` of maximal mass. -/
theorem corollary_5_12_winner_order {k : ℕ} (h : ℕ) (hh : 3 ≤ h) (p : PMF (Fin k))
    (i₁ : Fin k) (hmax : ∀ j, p j ≤ p i₁) :
    (∀ i : Fin k,
        winProb h p i ≤ (p i).toReal / (p i₁).toReal * winProb h p i₁ ∧
          (p i).toReal / (p i₁).toReal * winProb h p i₁ ≤ winProb h p i₁) ∧
      (p i₁).toReal ≤ winProb h p i₁ := by sorry

end HMajConsensus
