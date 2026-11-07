-- Prove2me | Theorems.Thm_MemoryRegret_lemma_6_2_mistake_concentration
-- name    : MemoryRegret.lemma_6_2_mistake_concentration
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:23.762914+00:00
-- url     : https://prove2.me/theorems/247c950f-3ff4-4ee1-9f30-0e2f1b8e744f
-- title:
--   Lemma 6.2 — any predictor's mistakes concentrate above the Bayes level
-- statement:
--   Let $\epsilon>0$, $T,m\in\mathbb N$ and let $Y_1,\dots,Y_T\in\{0,1\}$ be random variables with an arbitrary joint law, such that the Bayes-optimal predictor's mistake count $M^*$ satisfies
--   $$\mathbb E[M^*]\ge\frac T2-2T\epsilon^2\sqrt m.$$
--   Then for every (possibly randomized) prediction algorithm with mistake count $M$, and every $c>0$,
--   $$\Pr\Bigl[M\le T\Bigl(\frac12-\frac\epsilon c\Bigr)\Bigr]\le4c\epsilon\sqrt m+\exp\Bigl(-\frac{T\epsilon^2}{8c^2}\Bigr).$$
--
--   This upgrades the bound on the Bayes-optimal expectation to a high-probability bound for every predictor.
--
--   Differences from the source:
--   - encoding: random variables Y_1, …, Y_T → a probability vector P on {0,1}^T; reason: the law is all that the statement uses
--   - encoding: any (possibly randomized) prediction algorithm → a finite-seed mixture of deterministic predictors, the seed independent of Y; reason: with binary labels and a finite horizon every such algorithm has this form; the source proof also uses that the internal randomness is independent of the labels
-- source:
--   Brukhim, Garg, Memory-Regret Tradeoffs for Online Learning (manuscript, sha256 89bb0279…), Lemma 6.2, p.36

import Mathlib
import Definitions.Def_MemoryRegret_IsProbVec
import Definitions.Def_MemoryRegret_bayesMistakes
import Definitions.Def_MemoryRegret_RandOnlineAlg

namespace MemoryRegret

/-- **Lemma 6.2 (every predictor's mistakes concentrate above the Bayes level).**
Brukhim, Garg, *Memory-Regret Tradeoffs for Online Learning* (manuscript, sha256 89bb0279…),
Lemma 6.2, p.36.

Let `ϵ > 0`, `T, m ∈ ℕ`, and let `P` be any law of `(Y_1, …, Y_T) ∈ {0,1}^T` whose
Bayes-optimal predictor has `E[M*] ≥ T/2 − 2Tϵ²√m`. Then for every (possibly randomized)
prediction algorithm, with mistake count `M`, and every `c > 0`,
`Pr[M ≤ T(½ − ϵ/c)] ≤ 4cϵ√m + exp(−Tϵ²/(8c²))`.

**Formalization Note.** The algorithm is a `RandOnlineAlg Unit T Ω` (no instances): its seed
`ω ∼ seedLaw` is independent of `Y`, and its prediction at round `t` depends on `ω` and
`Y_0, …, Y_{t−1}`. The probability is over `Y ∼ P` and `ω`. -/
theorem lemma_6_2_mistake_concentration (ϵ : ℝ) (hϵ : 0 < ϵ) (T m : ℕ)
    (P : (Fin T → Bool) → ℝ) (hP : IsProbVec P)
    (hbayes : (T : ℝ) / 2 - 2 * T * ϵ ^ 2 * Real.sqrt m ≤ bayesMistakes P)
    {Ω : Type} [Fintype Ω] (A : RandOnlineAlg Unit T Ω) (c : ℝ) (hc : 0 < c) :
    ∑ y, P y * wprob A.seedLaw
        (fun ω => (A.algMistakes ω (fun t => ((), y t)) : ℝ) ≤ T * (1 / 2 - ϵ / c)) ≤
      4 * c * ϵ * Real.sqrt m + Real.exp (-(T * ϵ ^ 2) / (8 * c ^ 2)) := by sorry

end MemoryRegret
