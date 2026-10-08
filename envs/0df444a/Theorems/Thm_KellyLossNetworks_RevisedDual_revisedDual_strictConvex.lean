-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_revisedDual_strictConvex
-- name    : KellyLossNetworks.RevisedDual.revisedDual_strictConvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:04.168184+00:00
-- url     : https://prove2.me/theorems/5328b193-d5ce-43e6-b128-335e1af0627b
-- title:
--   §3.1, p. 338 — ∫₀^y U(z, C) dz and the objective of (3.5) are strictly convex
-- statement:
--   Consider a loss network with route rates $\nu_r>0$, link capacities $C_j\ge1$ and incidence matrix $A=(A_{jr})$ with entries in $\mathbb Z_+$, and let $U$ be the utilization function (3.4).
--
--   1. For every integer $c\ge1$, the function $y\mapsto\int_0^yU(z,c)\,dz$ is strictly convex on $[0,\infty)$.
--   2. The objective of the revised dual problem (3.5),
--   $$y\longmapsto\sum_r\nu_r\exp\Big(-\sum_jy_jA_{jr}\Big)+\sum_j\int_0^{y_j}U(z,C_j)\,dz,$$
--   is strictly convex on the cone $\{y\in\mathbb R^J: y\ge0\}$.
--
--   The first term of the objective is convex but in general not strictly convex (the matrix $A$ may have rank less than $J$); strict convexity of (3.5) comes from the integral terms, one for each coordinate.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, §3.1, the paragraph after (3.5)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **Strict convexity of the revised dual objective.** For every `c ≥ 1`, `y ↦ ∫_0^y U(z, c) dz` is
strictly convex on `[0, ∞)`; and if `ν_r > 0` for every route and `C_j ≥ 1` for every link, the
objective of the revised dual problem (3.5) is strictly convex on the cone `y ≥ 0`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, the paragraph after (3.5) (unnumbered).

**Formalization Note.** The first clause concerns a single capacity, named `c` to keep it apart
from the network's capacity vector `C`. -/
theorem revisedDual_strictConvex {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    (∀ c : ℕ, 1 ≤ c →
      StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun y : ℝ => ∫ z in (0 : ℝ)..y, U z c)) ∧
    StrictConvexOn ℝ {y : Fin J → ℝ | ∀ j, 0 ≤ y j} (revisedDualObjective A ν C) := by sorry

end KellyLossNetworks.RevisedDual
