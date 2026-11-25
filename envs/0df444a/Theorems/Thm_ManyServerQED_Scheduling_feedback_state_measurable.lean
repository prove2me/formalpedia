-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_feedback_state_measurable
-- name    : ManyServerQED.Scheduling.feedback_state_measurable
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:33:15.1597+00:00
-- url     : https://prove2.me/theorems/de550f6e-c149-5c70-9b0b-7509ef3e5292
-- title:
--   Measurability of every nonnegative-time section of an existing feedback trajectory
-- statement:
--   Let $F$ be a state-feedback allocation with $F(x)le x$ coordinatewise, and let an integer-valued queue trajectory $X$ satisfy the finite-server controlled balance equation under $F$. For every fixed $T\ge0$, the state $X(T)$ is measurable. The finite-event reconstruction recovers each state section from the renewal epochs, Poisson counts and the integer initial state, including on paths where several count jumps occur at the same calendar time.
-- source:
--   Atar, Mandelbaum and Reiman (2004), https://arxiv.org/abs/math/0407058, Definition 2 and Proposition 1, p. 12, and Appendix A.3, pp. 47–49.

import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory

namespace ManyServerQED.Scheduling

theorem feedback_state_measurable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X0 : Fin k → ℕ) (F : (Fin k → ℕ) → Fin k → ℕ)
    (hF : ∀ v i, F v i ≤ v i) (X : Ω → ℝ → Fin k → ℕ)
    (hC : M.IsControlled n X0 (fun ω t i => (X ω t i : ℝ)) (fun ω t i => (F (X ω t) i : ℝ))) :
    ∀ T : ℝ, 0 ≤ T → Measurable (fun ω => X ω T) := by sorry

end ManyServerQED.Scheduling
