-- Prove2me | Theorems.Thm_MetricalTaskSystem_Randomized_uniform_minDetExpCost_ge
-- name    : MetricalTaskSystem.Randomized.uniform_minDetExpCost_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:19:51.125956+00:00
-- url     : https://prove2.me/theorems/ac0f52ed-e0e5-41d4-bd92-8b2041aa80f1
-- title:
--   Section 7, lower bound — under uniform unit elementary tasks, $m_j\ge j/n$
-- statement:
--   Let $(S,d)$ be the uniform task system on $n$ states and let $D$ generate each successive task independently and uniformly from the unit elementary tasks $U_s$ ($U_s$ costs $1$ in state $s$ and $0$ elsewhere). Then for every initial state $s_0$ and every $j\ge 0$,
--   $$m_j=\inf_A E\big(c_A(\mathbf T^j)\big)\ge\frac jn ,$$
--   the infimum being over all deterministic on-line algorithms $A$.
--
--   This is the numerator estimate in the application of Lemma 7.2 that proves $\bar w(S,d)\ge H(n)$.
--
--   **Formalization Note** The task distribution is the product of uniform distributions on $S$, with $s$ identified with $U_s$; the state set carries a measurable space with measurable singletons.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 760, Section 7, proof of Theorem 7.1 (lower bound), first claim

import Mathlib
import Definitions.Def_MetricalTaskSystem_Randomized_Model
import Definitions.Def_MetricalTaskSystem_Randomized_TaskDistribution

namespace MetricalTaskSystem.Randomized

/-- **Section 7, proof of the lower bound, first claim** (Borodin–Linial–Saks 1992, p. 760).
On the uniform task system with `n = |S|` states, let the tasks be independent and uniformly
distributed unit elementary tasks `U_s`. Then for every initial state `s₀` and every `j`,
`m_j ≥ j / n`: every deterministic on-line algorithm has expected cost at least `j / n` on the
first `j` tasks. -/
theorem uniform_minDetExpCost_ge {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [MeasurableSpace S] [MeasurableSingletonClass S] (s₀ : S) (j : ℕ) :
    (j : ℝ) / Fintype.card S ≤
      minDetExpCost (uniformD (S := S)) s₀ (unitTask (S := S)) (uniformStateSeq S) j := by sorry

end MetricalTaskSystem.Randomized
