-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_utilization_strictMono
-- name    : KellyLossNetworks.RevisedDual.utilization_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:08:58.051023+00:00
-- url     : https://prove2.me/theorems/79b42c85-596d-4b67-9c8e-809a434b53a1
-- title:
--   §3.1, p. 338 — U(y, C) is a strictly increasing function of y
-- statement:
--   Let $C\ge1$ be an integer and $U$ the utilization function defined by (3.4). Then
--   $$y\longmapsto U(y,C)\quad\text{is strictly increasing on }[0,\infty).$$
--
--   In the single-link Erlang model, $U(y,C)$ is the mean number of busy circuits when the blocking probability is $1-e^{-y}$; more blocking means more circuits in use. This monotonicity is what makes the integral terms of the revised dual problem (3.5) strictly convex.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, §3.1, the paragraph after (3.4)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **`U(y, C)` is a strictly increasing function of `y`.** For `C ≥ 1`, `y ↦ U(y, C)` is
strictly increasing on `[0, ∞)`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, the paragraph after (3.4) (unnumbered). -/
theorem utilization_strictMono (C : ℕ) (hC : 1 ≤ C) :
    StrictMonoOn (fun y : ℝ => U y C) (Set.Ici 0) := by sorry

end KellyLossNetworks.RevisedDual
