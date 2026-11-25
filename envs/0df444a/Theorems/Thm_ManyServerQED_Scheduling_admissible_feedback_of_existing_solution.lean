-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_admissible_feedback_of_existing_solution
-- name    : ManyServerQED.Scheduling.admissible_feedback_of_existing_solution
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:21:42.124065+00:00
-- url     : https://prove2.me/theorems/c599126e-14cd-4cc8-b543-3f073c2f3cdb
-- title:
--   An existing controlled state-feedback solution has an admissible SCP version
-- statement:
--   Fix a feasible state-feedback rule $F$ in the $n$-server queue and suppose a nonnegative integer-valued controlled state $X$ already solves the balance equations with service vector $F(X)$. There is an admissible scheduling control policy with state $Y$ and service vector $F(Y)$ such that
--   $$Y(omega,t)=X(omega,t)qquad(tge 0)$$
--   for every sample point. The version permits a choice of the values at negative times, which do not enter the queue equations or the information fields. This conditional form suffices for the preemptive optimality theorem, where the feedback solution is given.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, Proposition 1 (p. 12), Appendix A.3 (pp. 47–49), and the use in Theorem 2(i). This is the admissibility part conditional on an existing solution.

import Definitions.Def_ManyServerQED_Scheduling_Policy

namespace ManyServerQED.Scheduling

theorem admissible_feedback_of_existing_solution
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ)
    (hn : 1 ≤ n) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → (Fin k → ℕ))
    (hF_le : ∀ X i, F X i ≤ X i) (hF_sum : ∀ X, ∑ i, F X i ≤ n)
    (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ))) :
    ∃ Y : Ω → ℝ → Fin k → ℕ,
      (∀ ω t, 0 ≤ t → X ω t = Y ω t) ∧
      M.IsSCP n X0 (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F (Y ω t) i : ℝ)) ∧
      M.IsAdmissible n (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F (Y ω t) i : ℝ)) := by sorry

end ManyServerQED.Scheduling
