-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_rank_unique
-- name    : KellyLossNetworks.Primal.rank_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:07:26.25124+00:00
-- url     : https://prove2.me/theorems/fbd86fc1-a896-4ab8-ab61-9e862ff21879
-- title:
--   Full row rank gives a unique dual optimum
-- statement:
--   If the real incidence matrix $A$ has rank $J$, the number of links, and all capacities satisfy $C_j\ge1$, then the dual objective is strictly convex on $y\ge0$ and has exactly one minimizer there:
--
--   $$\operatorname{rank}_{\mathbb R}(A)=J\quad\Longrightarrow\quad \exists!\,y\ge0\;\text{minimizing }D(y).$$
--
--   This yields uniqueness of the blocking solution under full row rank. Positive offered traffic is assumed for every route.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 328–329, §2.1, paragraph preceding Theorem 2.8

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, pp. 328–329, the paragraph preceding Theorem 2.8.
The matrix rank is the number of links, not the number of routes. -/
theorem rank_unique {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (hC : ∀ j, 1 ≤ C j)
    (hrank : (Matrix.of fun j r => (A j r : ℝ)).rank = J) :
    StrictConvexOn ℝ {y : Fin J → ℝ | ∀ j, 0 ≤ y j}
      (KellyStochasticNetworks.dualObjective A ν C) ∧
    ∃! y : Fin J → ℝ, IsDualOpt A ν C y := by sorry

end KellyLossNetworks.Primal
