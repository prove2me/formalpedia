-- Prove2me | Theorems.Thm_MemoSDPI_Main_lemma_4_1
-- name    : MemoSDPI.Main.lemma_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:43:01.192735+00:00
-- url     : https://prove2.me/theorems/7c9f1641-0141-4079-847d-a853e570a998
-- title:
--   Lemma 4.1 — a k-set that lands in the first t places of a uniform permutation carries p(s log(m/t) − log C(k,s)) − log 2 nats
-- statement:
--   Let $\pi$ be a uniformly random permutation of $[m]$, and let $T$ be a $k$-element subset of $[m]$ jointly distributed with $\pi$. Let $t < m$, $1 \le s \le \min\{k, t\}$ and $p \in [0,1]$. If $\Pr\big[|T \cap \{\pi(1),\dots,\pi(t)\}| \ge s\big] \ge p$, then
--   $$
--   I(T; \pi) \;\ge\; p\Big(s \log\frac{m}{t} - \log\binom{k}{s}\Big) - \log 2 .
--   $$
--   In particular, if $T \subseteq \{\pi(1), \dots, \pi(t)\}$ with probability at least $p$, then $I(T;\pi) \ge pk\log(m/t) - \log 2$.
--
--   The lemma turns accuracy of a selection into information about the ordering of the means (Theorem 4.2).
--
--   **Formalization Note** The joint law $\mu$ of $(\pi, T)$ is any probability measure on permutations $\times$ $k$-subsets whose first marginal is uniform. Places are $0$-based: $\{\pi(1),\dots,\pi(t)\}$ is `firstPlaces π t` $=\{\pi(i) : i < t\}$. The real lower bounds enter through `ENNReal.ofReal` (a negative bound becomes $0$, and $I \ge 0$ anyway). Both conclusions are stated, the second for every $p\in[0,1]$.
--
--   Differences from the source:
--   - encoding: π(1), …, π(t) (1-based places) → firstPlaces π t = {π i : i.val < t} in Fin m; reason: 0-based indices; same sets
--   - encoding: real lower bound on I(T; π) ∈ [0, ∞] → ENNReal.ofReal (bound) ≤ I; reason: equivalent: I ≥ 0, so a negative bound holds trivially in both readings
--   - encoding: T jointly distributed with a uniform π → μ on Perm (Fin m) × KSubset m k with μ.map Prod.fst = uniformPerm m; reason: the joint law with uniform first marginal
--   - generalization: the "In particular" clause under the lemma's hypotheses t < m and 1 ≤ s ≤ min{k, t} (so 1 ≤ k and 1 ≤ t) → the second conjunct for every k and every t < m; reason: the extra cases k = 0 and t = 0 are trivially true (for k = 0 the bound is −log 2 < 0; for t = 0 < k the event T ⊆ ∅ is empty, so p = 0 and the bound is −log 2), and on 1 ≤ k, 1 ≤ t the conjunct is the printed clause
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 15, Lemma 4.1

import Mathlib
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_Selection

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 15, Lemma 4.1: for a uniformly random permutation `π` of `[m]` and a `k`-subset
`T` jointly distributed with it, `t < m`, `1 ≤ s ≤ min{k, t}`, `p ∈ [0, 1]`: if
`Pr[|T ∩ {π(1), …, π(t)}| ≥ s] ≥ p` then `I(T; π) ≥ p (s log(m/t) − log C(k, s)) − log 2`; and if
`T ⊆ {π(1), …, π(t)}` with probability at least `p`, then `I(T; π) ≥ p k log(m/t) − log 2`. -/
theorem lemma_4_1 {m k : ℕ} (μ : Measure (Equiv.Perm (Fin m) × KSubset m k))
    [IsProbabilityMeasure μ] (hπ : μ.map Prod.fst = uniformPerm m) (t : ℕ) (ht : t < m) :
    (∀ (s : ℕ) (p : ℝ), 1 ≤ s → s ≤ min k t → 0 ≤ p → p ≤ 1 →
        ENNReal.ofReal p ≤ μ {x | s ≤ (x.2.toFinset ∩ firstPlaces x.1 t).card} →
        ENNReal.ofReal (p * ((s : ℝ) * Real.log ((m : ℝ) / t) - Real.log (k.choose s : ℝ))
            - Real.log 2) ≤
          ThompsonTutorial.InfoRatio.mutualInfo μ (fun x => x.2) (fun x => x.1)) ∧
      (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
        ENNReal.ofReal p ≤ μ {x | x.2.toFinset ⊆ firstPlaces x.1 t} →
        ENNReal.ofReal (p * (k : ℝ) * Real.log ((m : ℝ) / t) - Real.log 2) ≤
          ThompsonTutorial.InfoRatio.mutualInfo μ (fun x => x.2) (fun x => x.1)) := by sorry

end MemoSDPI.Main
