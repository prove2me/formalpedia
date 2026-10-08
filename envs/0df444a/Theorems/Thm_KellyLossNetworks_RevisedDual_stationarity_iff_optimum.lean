-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_stationarity_iff_optimum
-- name    : KellyLossNetworks.RevisedDual.stationarity_iff_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:12.493266+00:00
-- url     : https://prove2.me/theorems/546d1bdd-9a36-4805-8ddf-fe54b7543ab6
-- title:
--   §3.1, (3.6), p. 338 — y ≥ 0 is optimal for (3.5) iff the stationarity conditions (3.6) hold
-- statement:
--   Consider a loss network with route rates $\nu_r>0$, link capacities $C_j\ge1$ and incidence matrix $A=(A_{jr})$ with entries in $\mathbb Z_+$, and let $y\in\mathbb R^J$ with $y\ge0$. Then $y$ is an optimum of the revised dual problem (3.5) if and only if
--   $$\sum_rA_{jr}\,\nu_r\exp\Big(-\sum_iy_iA_{ir}\Big)=U(y_j,C_j),\qquad j=1,\dots,J. \tag{3.6}$$
--
--   The conditions (3.6) are obtained by differentiating the objective of (3.5) in each coordinate; they locate the unique optimum.
--
--   **Formalization Note** (3.6) is an equality also at a coordinate with $y_j=0$, where optimality over $y\ge0$ gives only a one-sided condition. The two agree because $U(0,C)=0$ and the left side of (3.6) is nonnegative.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, §3.1, (3.6)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **The stationarity conditions (3.6) locate the optimum.** If `ν_r > 0` for every route and
`C_j ≥ 1` for every link, a vector `y ≥ 0` is an optimum of the revised dual problem (3.5) if and
only if it satisfies the stationarity conditions (3.6),
`Σ_r A_jr ν_r exp(−Σ_i y_i A_ir) = U(y_j, C_j)` for `j = 1, …, J`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, (3.6).

**Formalization Note.** (3.6) is an equality also at a boundary coordinate `y_j = 0`, where
optimality over `y ≥ 0` gives only a one-sided condition; the two agree because `U(0, C) = 0`
and the left side of (3.6) is nonnegative. -/
theorem stationarity_iff_optimum {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) (y : Fin J → ℝ)
    (hy : ∀ j, 0 ≤ y j) :
    IsRevisedDualOptimum A ν C y ↔ StationarityConditions A ν C y := by sorry

end KellyLossNetworks.RevisedDual
