-- Prove2me | Theorems.Thm_HMajConsensus_theorem_6_1_plurality_good
-- name    : HMajConsensus.theorem_6_1_plurality_good
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:15:53.404944+00:00
-- url     : https://prove2.me/theorems/da56c73c-0f68-4c75-afbe-c8412411db98
-- title:
--   Theorem 6.1 — from a good configuration, plurality consensus in $O(\ln n/\gamma(0))$ rounds w.p. $\ge1-1/n$
-- statement:
--   Let $h\ge3$ and $2\le k\le n$, and let $i_0$ be a reference opinion. There are absolute constants $K>0$ (the constant $C$ of (⋆)) and $C'>0$ such that, if the initial configuration is good in the sense of (⋆),
--   $$\Delta(0)\ \ge\ K\sqrt{\frac{p_{i_0}(0)}{\gamma(0)}\cdot\frac{\ln n}{n}},\qquad \gamma(0)=\min\{h^2p_{i_0}(0),1\},$$
--   then plurality consensus (all nodes hold $i_0$) is reached within $C'\ln n/\gamma(0)$ rounds with probability at least $1-1/n$.
--
--   This is the plurality-consensus theorem of §6, a reformulation of Theorem 1.2.
--
--   **Formalization Note** $K$ and $C'$ are chosen before $n,k,h$, the configuration and $i_0$; a larger $K$ only strengthens the hypothesis, so this is the statement for every sufficiently large $K$. "Within $x$ rounds" is some round $t\in\mathbb N$ with $t\le x$.
--
--   Differences from the source:
--   - encoding: opinion 1 of §6 (other opinions not sorted, p.28) → a label i₀ : Fin k; reason: §6 fixes only which opinion is opinion 1; same instances
--   - encoding: sufficiently large / small constants, O, Ω and "with high probability" (≥ 1 − 1/n^c for some constant c > 0, p.2) → existential constants quantified before n, k, h and the initial configuration; reason: the paper's absolute-constant convention (p.2); uniformity in h and k is the content
--   - encoding: h-Majority as a sequence of random configurations (§2) → path law pathLaw h C₀ of the Markov kernel step h (product over nodes of Maj of h iid samples from p(C), uniform tie-breaking); reason: the §2 rule written as a kernel; the published Ionescu-Tulcea chain law gives the process
--   - encoding: nodes [n], opinions [k]; log n and ln n → Fin n, Fin k (0-based labels); Real.log; reason: Lean convention; the paper's log is natural (Lemma 6.9 and 7.2 proofs turn exp(−A log n) into n^{−A}); same instances
-- source:
--   d'Amore, Rybicki, Shimizu, Shiraga, Vacus, Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics, arXiv:2610.40562, Theorem 6.1, p.29 (good: (⋆), p.29)

import Mathlib
import Definitions.Def_HMajConsensus_IsGood

open MeasureTheory ProbabilityTheory

namespace HMajConsensus

/-- **Theorem 6.1** (d'Amore, Rybicki, Shimizu, Shiraga, Vacus, *Nearly-Optimal Time-Sample Trade-off in Consensus Dynamics*, arXiv:2610.40562, §6, p.29): let `h ≥ 3`. If the configuration `p(0)` is good in the
sense of (⋆), then plurality consensus is reached in `O(ln n/γ(0))` rounds with probability at
least `1 − 1/n`.

**Formalization Note** Plurality consensus is consensus on the reference opinion `i₀`. The
good-constant `K` (the paper's `C`) and the `O` constant `C'` are chosen before `n, k, h` and the
configuration; a larger `K` only strengthens the hypothesis. -/
theorem theorem_6_1_plurality_good :
    ∃ K : ℝ, 0 < K ∧ ∃ C' : ℝ, 0 < C' ∧
      ∀ (n k h : ℕ), 2 ≤ k → k ≤ n → 3 ≤ h → ∀ (C₀ : Config n k) (i₀ : Fin k),
        IsGood K h C₀ i₀ →
        1 - 1 / (n : ℝ) ≤ (pathLaw h C₀ {ω | ∃ t : ℕ,
          (t : ℝ) ≤ C' * Real.log n / growthRate h C₀ i₀ ∧ ∀ v, ω t v = i₀}).toReal := by sorry

end HMajConsensus
