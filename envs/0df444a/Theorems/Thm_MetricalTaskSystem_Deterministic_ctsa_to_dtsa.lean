-- Prove2me | Theorems.Thm_MetricalTaskSystem_Deterministic_ctsa_to_dtsa
-- name    : MetricalTaskSystem.Deterministic.ctsa_to_dtsa
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:13:06.713987+00:00
-- url     : https://prove2.me/theorems/39780c0e-1b10-4429-9e16-c91bcfbb190a
-- title:
--   Lemma 3.1 — every on-line continuous-time algorithm is matched by an on-line discrete-time one
-- statement:
--   Let $(S,d)$ be a task system (triangle inequality, not necessarily symmetric). For every on-line continuous-time scheduling algorithm $A'$ there is an on-line discrete-time scheduling algorithm $A$ that performs at least as well as $A'$ on every task sequence:
--   $$c_A(\mathbf T)\ \le\ c_{A'}(\mathbf T)\qquad\text{for all finite nonnegative task sequences }\mathbf T\text{ and all initial states } s_0 .$$
--
--   This lemma allows the upper bounds of the paper to be proved for algorithms that move at non-integral times.
--
--   **Formalization Note** The printed statement says "at least as well as $A$"; the intended comparison is with $A'$, as the proof shows. A CTSA is in list form (pieces of each unit interval with nonnegative lengths summing to $1$); see the `ContinuousTime` definition.
-- source:
--   Borodin, Linial, Saks, An Optimal On-Line Algorithm for Metrical Task System, J. ACM 39(4) (1992), p. 752, Lemma 3.1

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_ContinuousTime

namespace MetricalTaskSystem.Deterministic

/-- **Lemma 3.1** (Borodin–Linial–Saks 1992, p. 752). For any on-line continuous-time
scheduling algorithm `A'` there is an on-line discrete-time scheduling algorithm `A` that
performs at least as well as `A'` on every (nonnegative) task sequence, from every initial
state. -/
theorem ctsa_to_dtsa {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsTaskSystem d) (A' : CTSA S) (hA' : IsCTSA A') :
    ∃ A : OnlineAlgorithm S, ∀ (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ), (∀ i s, 0 ≤ T i s) →
      onlineCost d A s₀ T ≤ ctsaCost d A' s₀ T := by sorry

end MetricalTaskSystem.Deterministic
