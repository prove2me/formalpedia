-- Prove2me | Theorems.Thm_InfluencerAuth_Turnover_proposition_3
-- name    : InfluencerAuth.Turnover.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:12.418351+00:00
-- url     : https://prove2.me/theorems/806437b4-47cc-4587-bb4e-92c3adeb60fa
-- title:
--   Proposition 3, p. 9 — under Condition 2, (1−γ)x/(r+β−x) > γφ − 1, always being authentic is optimal from every A₀ ∈ (0, (β−x)/β)
-- statement:
--   Consider the influencer model with follower turnover: awareness evolves by $\frac{dA_t}{dt} = \beta F_t(1 - A_t) - x A_t$, where $F_t = A_t$ if she is authentic and $F_t = \gamma A_t$ if inauthentic, and instantaneous profit is $A_t$ or $\gamma\varphi A_t$ respectively; she maximizes $\int_0^\infty e^{-rt}\pi_t\,dt$ over all measurable policies. Assume the standing assumptions of the paper,
--   $$
--   0 < \gamma < 1,\qquad \varphi > 1,\qquad \gamma\varphi > 1,\qquad \beta > 0,\qquad r > 0,
--   $$
--   a turnover rate $x \in (0, \beta)$, and **Condition 2**:
--   $$
--   \frac{(1-\gamma)x}{r + \beta - x} > \gamma\varphi - 1 .
--   $$
--   Then for every feasible initial awareness level $A_0 \in \left(0, \frac{\beta - x}{\beta}\right)$ the policy of always being authentic is optimal: there is an admissible awareness path $A$ from $A_0$ under the always-authentic policy whose discounted profit is at least that of every measurable policy with any of its admissible paths from $A_0$.
--
--   In words: if the rate of turnover is high enough that Condition 2 holds, the influencer always stays authentic. High turnover keeps a large pool of unaware potential followers and makes any temporary loss of awareness costly, so the growth motive dominates the monetization motive at every feasible awareness level.
--
--   **Formalization Note** "Always stays authentic" is rendered as "the always-authentic policy $S = \emptyset$, with its path, is optimal from $A_0$"; the path is produced, not assumed. The range of $A_0$ is the paper's "all feasible levels of awareness, $A_t \in (0, (\beta - x)/\beta)$" (p. 9); above the steady state $(\beta-x)/\beta$ the claim is not made. The hypothesis $r > 0$ is the reading of "discount rate $r$" and makes the discounted profit finite. The standing assumption $\gamma\varphi > 1$ is the paper's assumption "for the remainder of the paper" (p. 5) and is kept.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), Proposition 3, p. 9 (with the standing assumptions of §3, pp. 4–5)

import Mathlib
import Definitions.Def_InfluencerAuth_Turnover_Model

namespace InfluencerAuth.Turnover

theorem proposition_3 (γ φ β r x : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1) (hφ : 1 < φ) (hβ : 0 < β)
    (hr : 0 < r) (hγφ : 1 < γ * φ) (hx : 0 < x) (hxβ : x < β)
    (hC2 : Condition2 γ φ β r x) :
    ∀ A₀ ∈ Set.Ioo (0 : ℝ) ((β - x) / β), ∃ A : ℝ → ℝ, IsOptimalFrom β γ φ r x A₀ ∅ A := by sorry

end InfluencerAuth.Turnover
