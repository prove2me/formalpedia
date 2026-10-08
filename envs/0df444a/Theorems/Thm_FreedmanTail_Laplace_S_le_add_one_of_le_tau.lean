-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_S_le_add_one_of_le_tau
-- name    : FreedmanTail.Laplace.S_le_add_one_of_le_tau
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:29.589901+00:00
-- url     : https://prove2.me/theorems/8705fe39-bec2-4a1e-97a4-135b8be57216
-- title:
--   Proof of (1.8), (4.2), p. 108 — S_n ≤ a + 1 for n ≤ τ_a
-- statement:
--   Under condition (1.1) ($X_n$ $\mathcal F_n$-measurable, $|X_n| \le 1$, $E\{X_n \mid \mathcal F_{n-1}\} = 0$ for $n \ge 1$), fix $a > 0$ and let $\tau_a$ be the first $n$ with $S_n \ge a$ ($\tau_a = \infty$ if none), as in Definition (1.7). Then, almost surely,
--   $$
--   S_n \le a + 1 \qquad \text{for every } n \le \tau_a .
--   $$
--
--   The partial sums cannot overshoot the level $a$ by more than one step, and a step has size at most $1$. This bound makes the stopped submartingale of Proposition (3.6) controllable at the crossing time.
--
--   **Formalization Note** "Almost surely" because $|X_n| \le 1$ is assumed almost surely; $n$ ranges over all natural numbers with $n \le \tau_a$ (all $n$ when $\tau_a = \infty$), including $n = 0$, where $S_0 = 0$.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 108 (PDF p. 9), (4.2) The proof of (1.8), first sentence

import Mathlib
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (4.2), p. 108, first sentence: under condition (1.1), with `a > 0`,
almost surely `S_n ≤ a + 1` for every `n ≤ τ_a`. -/
theorem S_le_add_one_of_le_tau {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (a : ℝ) (ha : 0 < a) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, (n : WithTop ℕ) ≤ tau a X ω → FreedmanTail.Bernstein.S X n ω ≤ a + 1 := by sorry

end FreedmanTail.Laplace
