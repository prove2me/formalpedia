-- Prove2me | Theorems.Thm_NonlinSSD_Discrete_theorem_7_duality
-- name    : NonlinSSD.Discrete.theorem_7_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:03:46.143873+00:00
-- url     : https://prove2.me/theorems/682a6993-1855-47b1-80d3-6f9bfe2ae600
-- title:
--   Theorem 7 — under Slater, the dual problem (48) over utilities in V_i has a solution and no duality gap
-- statement:
--   Under the standing assumptions and the Slater condition of Theorem 6, let
--   $$D(u, \theta) = \sup_{z \in Z,\ X \in \mathbb R^{mn}} L(z, X, u, \theta) \tag{47}$$
--   be the dual functional, an extended real number, and consider the dual problem
--   $$\min\Big\{D(u, \theta) : u \in V_1 \times \dots \times V_m,\ \theta \in \mathbb R^{mn},\ \theta \ge 0\Big\}. \tag{48}$$
--
--   1. If problem (38)–(41) has an optimal solution $(\hat z, \hat X)$, then the dual problem (48) has an optimal solution $(\hat u, \hat\theta)$, and $D(\hat u, \hat\theta) = \sum_j p_j h_j(\hat z)$: the optimal values coincide.
--   2. For every solution $(\hat u, \hat\theta)$ of the dual problem, any maximizer $(\hat z, \hat X)$ of $L(\cdot, \cdot, \hat u, \hat\theta)$ over $Z \times \mathbb R^{mn}$ that satisfies (39)–(40) and (44)–(45) is an optimal solution of (38)–(41).
--
--   This is the duality theorem for the finite-scenario problem, the basis of the decomposition (49)–(51) of the dual functional.
--
--   **Formalization Note.** $D$ takes values in `EReal` (a supremum of an unbounded family is $+\infty$). A solution of (48) is a feasible $(\hat u, \hat\theta)$ with $D(\hat u, \hat\theta) \le D(u, \theta)$ for every feasible $(u, \theta)$. The primal optimal value is the objective at any optimal solution.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 18, Theorem 7 with Eqs. (47)–(48)

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

namespace NonlinSSD.Discrete

theorem theorem_7_duality {m n N : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (Z : Set (Fin N → ℝ)) (hZ : Convex ℝ Z)
    (h : Fin n → (Fin N → ℝ) → ℝ) (hh : ∀ j, ConcaveOn ℝ Set.univ (h j))
    (g : Fin m → Fin n → (Fin N → ℝ) → ℝ) (hg : ∀ i j, ConcaveOn ℝ Set.univ (g i j))
    (y : Fin m → Fin n → ℝ) (hS : SlaterCondition p Z g y) :
    (∀ (zh : Fin N → ℝ) (Xh : Fin m → Fin n → ℝ), IsOptimal p Z h g y zh Xh →
      ∃ (uh : Fin m → ℝ → ℝ) (θh : Fin m → Fin n → ℝ),
        (∀ i, InV (y i) (uh i)) ∧ (∀ i j, 0 ≤ θh i j) ∧
        -- (û, θ̂) solves the dual problem (48)
        (∀ (u : Fin m → ℝ → ℝ) (θ : Fin m → Fin n → ℝ),
          (∀ i, InV (y i) (u i)) → (∀ i j, 0 ≤ θ i j) →
          dualFunctional p Z h g y uh θh ≤ dualFunctional p Z h g y u θ) ∧
        -- the optimal values coincide
        dualFunctional p Z h g y uh θh = ((objective p h zh : ℝ) : EReal)) ∧
    (∀ (uh : Fin m → ℝ → ℝ) (θh : Fin m → Fin n → ℝ),
      (∀ i, InV (y i) (uh i)) → (∀ i j, 0 ≤ θh i j) →
      (∀ (u : Fin m → ℝ → ℝ) (θ : Fin m → Fin n → ℝ),
          (∀ i, InV (y i) (u i)) → (∀ i j, 0 ≤ θ i j) →
          dualFunctional p Z h g y uh θh ≤ dualFunctional p Z h g y u θ) →
      ∀ (zh : Fin N → ℝ) (Xh : Fin m → Fin n → ℝ),
        (zh ∈ Z ∧ ∀ z ∈ Z, ∀ X : Fin m → Fin n → ℝ,
            lagrangian p h g y z X uh θh ≤ lagrangian p h g y zh Xh uh θh) →
        DominanceConstraints p y Xh → (∀ i k, Xh i k ≤ g i k zh) →
        (∀ i, ∑ j, p j * (uh i (Xh i j) - uh i (y i j)) = 0) →
        (∀ i j, θh i j * (Xh i j - g i j zh) = 0) →
        IsOptimal p Z h g y zh Xh) := by sorry

end NonlinSSD.Discrete
