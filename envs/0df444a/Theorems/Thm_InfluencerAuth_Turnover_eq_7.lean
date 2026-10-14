-- Prove2me | Theorems.Thm_InfluencerAuth_Turnover_eq_7
-- name    : InfluencerAuth.Turnover.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:31:03.593175+00:00
-- url     : https://prove2.me/theorems/4e7dcd75-6221-4dd5-9d11-30c86e048e7a
-- title:
--   (7), §4.2, p. 9 — dV̄(A_t)/dA_t at A_t = (β−x)/β equals ∫ e^{−(r+β−x)(u−t)} du = 1/(r+β−x)
-- statement:
--   Let $\beta > 0$, $r > 0$ and $0 < x < \beta$, and let $\overline V$ be the always-authentic value function of Lemma 5. Then $\overline V$ is differentiable at the steady-state awareness level $A = \frac{\beta - x}{\beta}$, and
--   $$
--   \left.\frac{d\overline V(A)}{dA}\right|_{A = \frac{\beta - x}{\beta}} \;=\; \int_0^\infty e^{-(r + \beta - x)s}\,ds \;=\; \frac{1}{r + \beta - x}.
--   $$
--
--   This is the marginal value of awareness at the maximum feasible awareness level under turnover. It is the quantity that, compared with the extra profit from being inauthentic, yields Condition 2.
--
--   **Formalization Note** The derivative is the ordinary two-sided derivative of the function $A \mapsto \overline V(A)$; the point $(\beta - x)/\beta$ lies in $(0,1)$ and $\overline V$ is defined on a neighbourhood of it. The paper's integration variable $u - t$ is written $s$. As for Lemma 5, the parameters $\gamma, \varphi$ and their assumptions do not appear.
-- source:
--   Nistor, Selove, Villas-Boas, Management Science (Articles in Advance 2024), §4.2, (7), p. 9

import Mathlib
import Definitions.Def_InfluencerAuth_Turnover_Model

namespace InfluencerAuth.Turnover

theorem eq_7 (β r x : ℝ) (hβ : 0 < β) (hr : 0 < r) (hx : 0 < x) (hxβ : x < β) :
    HasDerivAt (authValue β x r)
        (∫ s in Set.Ioi (0 : ℝ), Real.exp (-(r + β - x) * s)) ((β - x) / β) ∧
      ∫ s in Set.Ioi (0 : ℝ), Real.exp (-(r + β - x) * s) = 1 / (r + β - x) := by sorry

end InfluencerAuth.Turnover
