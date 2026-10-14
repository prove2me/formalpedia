-- Prove2me | Theorems.Thm_OAI_AlternatingNS_trajectory_flow
-- name    : OAI.AlternatingNS.trajectory_flow
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-12T01:21:09.024054+00:00
-- url     : https://prove2.me/theorems/1c2065ce-ce45-4feb-873d-bc2038faaed5
-- title:
--   Global existence and uniqueness of particle trajectories for a smooth rapidly decaying velocity field
-- statement:
--   Let $U$ be a velocity field that is smooth on $[0,\infty)\times\mathbb R^3$ and rapidly decaying with all its derivatives; in particular $U$ is bounded and uniformly Lipschitz in space. Then there is a flow $X$ such that for every $a\in\mathbb R^3$ the curve $t\mapsto X(a,t)$ satisfies $X(a,0)=a$ and $\partial_tX(a,t)=U(t,X(a,t))$ for all $t\ge0$ (one-sided at $t=0$), and every curve with these properties agrees with $X(a,\cdot)$ on $[0,\infty)$.
--
--   This is the global Picard–Lindelöf theorem for a bounded, globally Lipschitz, continuous non-autonomous vector field, with uniqueness from Gronwall's inequality.
--
--   **Formalization Note** Fields are functions $\mathbb R\to\mathbb R^3\to E$ (`Field`); only $t\ge0$ matters. `Smooth` is $C^\infty$ on $[0,\infty)\times\mathbb R^3$, `Rapid` bounds $(1+t+\|x\|)^J\|\partial_t^l\partial_x^\alpha F\|$ for all $J,l,\alpha$, `SupportedIn F K` means $\operatorname{supp}F(t,\cdot)\subseteq K$ for $t\ge0$, `residual ν U` is $\partial_tU+(U\cdot\nabla)U-\nu\Delta U$, and time derivatives are taken within $[0,\infty)$. All notions are those of the published definition `NavierStokesAlternating`.
-- source:
--   OpenAI, "Computation under Rapidly Vanishing Navier–Stokes Forcing" (September 27, 2026), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf; goal theorem OAI.AlternatingNS.alternating of the mission "Computation under Rapidly Vanishing Navier–Stokes Forcing"; classical global Picard–Lindelöf theorem and Gronwall uniqueness (e.g. P. Hartman, Ordinary Differential Equations, Ch. II)

import Mathlib
import Definitions.Def_NavierStokesAlternating

namespace OAI

open scoped BigOperators ENNReal Topology ContDiff

open MeasureTheory

namespace AlternatingNS

/-- **Global particle trajectories.** A smooth, rapidly decaying velocity field (in particular
bounded and uniformly Lipschitz in space) has, from every initial point, a trajectory defined for
all `t ≥ 0`, and it is unique on `[0, ∞)`. -/
theorem trajectory_flow (U : Velocity) (hU : Smooth U) (hr : Rapid U) :
    ∃ X : Space → ℝ → Space,
      (∀ a, IsTrajectory U a (X a)) ∧
      (∀ a γ, IsTrajectory U a γ → ∀ t, 0 ≤ t → γ t = X a t) := by
  sorry

end AlternatingNS
end OAI
