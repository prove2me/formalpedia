-- Prove2me | Theorems.Thm_HMajConsensus_theorem_5_1_relative_drift
-- name    : HMajConsensus.theorem_5_1_relative_drift
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:14:09.340787+00:00
-- url     : https://prove2.me/theorems/71fb3ce3-c3df-49c9-af45-9b8f5a8e5f7b
-- title:
--   Theorem 5.1 — expected relative drift $q_1/q_i\ge1+(p_1/p_i-1)(1+\frac1{80}\min\{h^2p_1,1\})$
-- statement:
--   Let $p=(p_1,\dots,p_k)$ be a probability vector and $h\ge3$. Let $X\sim\mathrm{Multinomial}(h;p)$ and $W_i=\{\mathrm{Maj}(X)=i\}$, where $\mathrm{Maj}$ breaks ties uniformly; write $q_i=\Pr[W_i]$. Let opinion $1$ have the largest mass, $p_1=\max_jp_j$. Then for every $i\in[k]$ with $p_i>0$,
--   $$\frac{q_1}{q_i}=\frac{\Pr[W_1]}{\Pr[W_i]}\ \ge\ 1+\Big(\frac{p_1}{p_i}-1\Big)\Big(1+\frac1{80}\min\{h^2p_1,1\}\Big).$$
--
--   This one-round estimate quantifies how $h$-Majority amplifies the lead of the plurality opinion relative to any other opinion; the factor $\min\{h^2p_1,1\}$ is the growth rate that sets every time scale of the paper.
--
--   **Formalization Note** $q_i$ is `winProb h p i`, the probability that the uniformly tie-broken majority of $h$ iid samples from $p$ is $i$. The ratio is a real division; $q_i>0$ whenever $p_i>0$.
--
--   Differences from the source:
--   - generalization: p = p(t), the current empirical distribution, sorted p₁ ≥ ··· ≥ p_k (§5, p.14) → every probability vector p : PMF (Fin k) and any label i₁ with p_{i₁} = max_j p_j, the other entries unsorted; reason: p(t) sorted is the case i₁ = the first label; the proof uses only p₁ = max_j p_j (the form of Lemma 3.1, p.6)
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 5.1, p.14

import Mathlib
import Definitions.Def_HMajConsensus_majLaw

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Theorem 5.1** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §5.1, p.14): let `h ≥ 3` and `i ∈ [k]` with `p_i > 0`; then
`q₁/q_i = Pr[W₁]/Pr[W_i] ≥ 1 + (p₁/p_i − 1)(1 + (1/80)·min{h²p₁, 1})`.

**Formalization Note** §5 sorts `p₁ ≥ ⋯ ≥ p_k`; only `p₁ = max_j p_j` is used, so "opinion 1"
is any label `i₁` of maximal mass (Lemma 3.1's form). `q_i = winProb h p i`; the ratio is a real
division, and `q_i > 0` whenever `p_i > 0`. -/
theorem theorem_5_1_relative_drift {k : ℕ} (h : ℕ) (hh : 3 ≤ h) (p : PMF (Fin k))
    (i₁ : Fin k) (hmax : ∀ j, p j ≤ p i₁) (i : Fin k) (hi : 0 < (p i).toReal) :
    1 + ((p i₁).toReal / (p i).toReal - 1) *
        (1 + (1 / 80) * min ((h : ℝ) ^ 2 * (p i₁).toReal) 1) ≤
      winProb h p i₁ / winProb h p i := by sorry

end HMajConsensus
