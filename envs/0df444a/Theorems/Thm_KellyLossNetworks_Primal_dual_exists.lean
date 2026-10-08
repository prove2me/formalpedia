-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_dual_exists
-- name    : KellyLossNetworks.Primal.dual_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:07:16.223+00:00
-- url     : https://prove2.me/theorems/e33e766d-c8ab-4d84-a9f9-21b10d2dd440
-- title:
--   The dual problem has an optimum
-- statement:
--   For positive offered traffic $\nu_r$ and capacities $C_j\ge1$, the dual objective
--
--   $$D(y)=\sum_r\nu_r e^{-\sum_jy_jA_{jr}}+\sum_j y_j C_j$$
--
--   is convex on $y\ge0$ and attains its minimum there. This supplies a dual optimizer from which a solution of the blocking conditions can be obtained.
--
--   **Formalization Note** Positive capacities are stated explicitly because a zero capacity can invalidate the printed coercivity claim.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 328, §2.1, paragraph after (2.7)

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, p. 328, paragraph after (2.7).
Formalization Note: strictly positive capacities ensure coercivity; zero capacity invalidates
the printed coercivity assertion. -/
theorem dual_exists {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (hC : ∀ j, 1 ≤ C j) :
    ConvexOn ℝ {y : Fin J → ℝ | ∀ j, 0 ≤ y j}
      (KellyStochasticNetworks.dualObjective A ν C) ∧
    ∃ y : Fin J → ℝ, IsDualOpt A ν C y := by sorry

end KellyLossNetworks.Primal
