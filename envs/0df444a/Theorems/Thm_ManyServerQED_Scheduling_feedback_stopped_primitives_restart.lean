-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_feedback_stopped_primitives_restart
-- name    : ManyServerQED.Scheduling.feedback_stopped_primitives_restart
-- status  : Open
-- author  : @Jie Luo
-- created : 2026-11-25T18:33:14.883881+00:00
-- url     : https://prove2.me/theorems/c75dbd52-db70-5991-bb8e-302cc3534439
-- title:
--   Restart laws of independent primitives at the clocks of an existing feedback SCP
-- statement:
--   Fix a feasible state-feedback rule and an existing scheduling control policy using that rule. At any fixed time $t\ge0$ the observed queue history is independent of the future primitive increments used in Definition 2. The arrival increments begin at the first arrival no earlier than $t$, and each service or abandonment increment begins at the corresponding elapsed effort clock. Each resumed service and abandonment path has the law of its original Poisson process.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, Definition 2 and Proposition 1, p. 12, and Appendix A.3, pp. 47–49.

import Definitions.Def_ManyServerQED_Scheduling_Policy

namespace ManyServerQED.Scheduling

theorem feedback_stopped_primitives_restart
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (n : ℕ)
    (hn : 1 ≤ n) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → (Fin k → ℕ))
    (hF_le : ∀ X i, F X i ≤ X i) (hF_sum : ∀ X, ∑ i, F X i ≤ n)
    (X : Ω → ℝ → Fin k → ℕ)
    (hX : M.IsSCP n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ))) :
    M.IsAdmissible n (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ)) := by sorry

end ManyServerQED.Scheduling
