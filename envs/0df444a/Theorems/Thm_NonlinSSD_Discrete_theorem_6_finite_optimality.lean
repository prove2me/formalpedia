-- Prove2me | Theorems.Thm_NonlinSSD_Discrete_theorem_6_finite_optimality
-- name    : NonlinSSD.Discrete.theorem_6_finite_optimality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:03:30.788306+00:00
-- url     : https://prove2.me/theorems/6ef84f0e-805a-47de-b5da-6da83cc5d26b
-- title:
--   Theorem 6 — with finite scenarios and Slater's condition, optimality in (38)–(41) is characterized by utilities û_i ∈ V_i and θ̂ ≥ 0
-- statement:
--   Consider problem (38)–(41): maximize $\sum_{j=1}^n p_j h_j(z)$ over $z \in Z$ and $X = (x_{ij}) \in \mathbb R^{mn}$ subject to the dominance constraints (39) and the splitting constraints $x_{ik} \le g_{ik}(z)$ (40). The standing assumptions are: $p_j \ge 0$ with $\sum_j p_j = 1$; $Z \subseteq \mathbb R^N$ convex; every $h_j$ and $g_{ij}$ concave on $\mathbb R^N$. Assume the problem satisfies the Slater condition (some $\tilde z \in \operatorname{relint} Z$ and $\tilde X$ satisfy (39) and $\tilde x_{ik} < g_{ik}(\tilde z)$ for all $i, k$). Let $L$ be the Lagrangian (42).
--
--   1. If $(\hat z, \hat X)$ is an optimal solution of (38)–(41), then there exist $\hat u_i \in V_i$ and nonnegative vectors $\hat\theta_i \in \mathbb R^n$, $i = 1,\dots,m$, such that
--   $$L(\hat z, \hat X, \hat u, \hat\theta) = \max_{(z, X) \in Z \times \mathbb R^{mn}} L(z, X, \hat u, \hat\theta), \tag{43}$$
--   $$\sum_{j=1}^n p_j\big[\hat u_i(\hat x_{ij}) - \hat u_i(y_{ij})\big] = 0, \quad i \in I, \tag{44}$$
--   $$\hat\theta_{ij}\big(\hat x_{ij} - g_{ij}(\hat z)\big) = 0, \quad i \in I,\ j \in J. \tag{45}$$
--   2. Conversely, if for some $\hat u_i \in V_i$ and nonnegative $\hat\theta_i \in \mathbb R^n$ a maximizer $(\hat z, \hat X)$ of (43) satisfies (39)–(40) and (44)–(45), then $(\hat z, \hat X)$ is an optimal solution of (38)–(41).
--
--   The theorem is the finite-dimensional refinement of the paper's Theorem 2: the multiplier of each dominance constraint is a concave nondecreasing piecewise-linear utility with kinks at the realizations of the benchmark $Y_i$, and no uniform dominance condition (which fails here at the smallest realization) is needed.
--
--   **Formalization Note.** (43) is an attained maximum: $\hat z \in Z$ and $L(z, X, \hat u, \hat\theta) \le L(\hat z, \hat X, \hat u, \hat\theta)$ for all $z \in Z$ and all $X \in \mathbb R^{mn}$ (no constraints on $X$). "An optimal solution of (43)" in part 2 is read the same way. The Slater condition is a hypothesis of the whole statement, as printed; part 2 does not use it. The relative interior is `intrinsicInterior ℝ Z`. $V_i$ is encoded as described in the definition item (concave, nondecreasing, affine between consecutive realizations, $0$ to the right of $\max_k y_{ik}$); $p_j = 0$ is allowed.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 17, Theorem 6 with Eqs. (42)–(45); problem (38)–(41), Slater condition and V_i on p. 16; standing assumptions p. 2

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

namespace NonlinSSD.Discrete

theorem theorem_6_finite_optimality {m n N : ℕ} (p : Fin n → ℝ) (hp0 : ∀ j, 0 ≤ p j)
    (hp1 : ∑ j, p j = 1) (Z : Set (Fin N → ℝ)) (hZ : Convex ℝ Z)
    (h : Fin n → (Fin N → ℝ) → ℝ) (hh : ∀ j, ConcaveOn ℝ Set.univ (h j))
    (g : Fin m → Fin n → (Fin N → ℝ) → ℝ) (hg : ∀ i j, ConcaveOn ℝ Set.univ (g i j))
    (y : Fin m → Fin n → ℝ) (hS : SlaterCondition p Z g y) :
    (∀ (zh : Fin N → ℝ) (Xh : Fin m → Fin n → ℝ), IsOptimal p Z h g y zh Xh →
      ∃ (uh : Fin m → ℝ → ℝ) (θh : Fin m → Fin n → ℝ),
        (∀ i, InV (y i) (uh i)) ∧ (∀ i j, 0 ≤ θh i j) ∧
        -- (43): the maximum of L(·, ·, û, θ̂) over Z × ℝ^{mn} is attained at (ẑ, X̂)
        (zh ∈ Z ∧ ∀ z ∈ Z, ∀ X : Fin m → Fin n → ℝ,
          lagrangian p h g y z X uh θh ≤ lagrangian p h g y zh Xh uh θh) ∧
        -- (44)
        (∀ i, ∑ j, p j * (uh i (Xh i j) - uh i (y i j)) = 0) ∧
        -- (45)
        (∀ i j, θh i j * (Xh i j - g i j zh) = 0)) ∧
    (∀ (uh : Fin m → ℝ → ℝ) (θh : Fin m → Fin n → ℝ) (zh : Fin N → ℝ)
        (Xh : Fin m → Fin n → ℝ),
      (∀ i, InV (y i) (uh i)) → (∀ i j, 0 ≤ θh i j) →
      -- (ẑ, X̂) is an optimal solution of (43)
      (zh ∈ Z ∧ ∀ z ∈ Z, ∀ X : Fin m → Fin n → ℝ,
          lagrangian p h g y z X uh θh ≤ lagrangian p h g y zh Xh uh θh) →
      -- (39)–(40)
      DominanceConstraints p y Xh → (∀ i k, Xh i k ≤ g i k zh) →
      -- (44)–(45)
      (∀ i, ∑ j, p j * (uh i (Xh i j) - uh i (y i j)) = 0) →
      (∀ i j, θh i j * (Xh i j - g i j zh) = 0) →
      IsOptimal p Z h g y zh Xh) := by sorry

end NonlinSSD.Discrete
