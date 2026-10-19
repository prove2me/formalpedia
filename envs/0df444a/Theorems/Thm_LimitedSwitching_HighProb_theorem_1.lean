-- Prove2me | Theorems.Thm_LimitedSwitching_HighProb_theorem_1
-- name    : LimitedSwitching.HighProb.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:14:19.186436+00:00
-- url     : https://prove2.me/theorems/cbc88ea7-6c00-4fa1-be47-d4c5da96b984
-- title:
--   Theorem 1, p. 8 — some PFE algorithm has Regret_T, Switches_T ≤ C√(T log n log(1/δ)) with probability ≥ 1 − δ against every oblivious adversary
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. For all integers $T\ge1$ and $n\ge1$ and every $\delta\in(0,\tfrac12)$, there exists a randomized online algorithm $\mathcal A$ for prediction from experts with $n$ actions over $T$ rounds with this property. Its randomness $\omega$ is drawn from a probability space $(\Omega,\mu)$, and at round $t$ it sees $\omega$ and the past losses $\ell_1,\dots,\ell_{t-1}$. Then for every loss sequence $(\ell_t)$ with values in $[0,1]$ fixed in advance (an oblivious adversary),
--
--   $$\mathbb P\Big(\mathrm{Regret}_T(\mathcal A)\le C\sqrt{T\log n\log(1/\delta)}\ \text{ and }\ \mathrm{Switches}_T(\mathcal A)\le C\sqrt{T\log n\log(1/\delta)}\Big)\ge1-\delta.$$
--
--   The algorithm may depend on $T$, $n$ and $\delta$ (the paper notes that it is not uniform in $\delta$), but not on the loss sequence. In expectation, $O(\sqrt{T\log n})$ regret and switching are classical. This theorem gives the first high-probability version, with the optimal dependence on $\delta$. It is the basis of the paper's switching-budget and switching-cost results.
--
--   **Formalization Note** The $O(\cdot)$ is an absolute constant $C$, quantified before $T$, $n$ and $\delta$. An online algorithm is a function of its randomness, the round and the past losses only, so it cannot see the current or future losses. The loss sequence is quantified after the algorithm. Following the paper's reduction (p. 5), the oblivious adversary is a deterministic loss sequence. The probability statement bounds the outer measure of the failure event by $\delta$, so no measurability side condition is needed. For $n=1$ the bound reads $0$, and regret and switches are indeed $0$.
-- source:
--   Altschuler & Talwar, Online learning over a finite action set with limited switching, arXiv:1803.01548v2, p. 8, Theorem 1

import Mathlib
import Definitions.Def_LimitedSwitching_HighProb_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LimitedSwitching.HighProb

theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (T n : ℕ), 1 ≤ T → 1 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
        ∃ A : OnlineAlg Ω n, ∀ ℓ : ℕ → Fin n → ℝ, IsLossSeq ℓ →
          μ {ω | ¬ (regret T ℓ (play A ω ℓ) ≤ C * √(T * Real.log n * Real.log (1 / δ)) ∧
              (switches T (play A ω ℓ) : ℝ) ≤ C * √(T * Real.log n * Real.log (1 / δ)))}
            ≤ ENNReal.ofReal δ := by sorry

end LimitedSwitching.HighProb
