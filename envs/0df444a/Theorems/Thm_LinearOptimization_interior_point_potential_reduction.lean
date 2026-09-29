-- Prove2me | Theorems.Thm_LinearOptimization_interior_point_potential_reduction
-- name    : LinearOptimization.interior_point_potential_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:46:04.479841+00:00
-- url     : https://prove2.me/theorems/ce5ef26e-06e5-4143-9daa-548fc344675a
-- title:
--   Constant potential reduction yields an explicit iteration bound
-- statement:
--   **(Theorem 9.4, p. 410 — generic potential-reduction iteration bound, Section 9.3)** Define the potential function
--
--   $$G(\mathbf{x}, \mathbf{s}) = q\log \mathbf{s}'\mathbf{x} - \sum_{j=1}^n \log x_j - \sum_{j=1}^n \log s_j,$$
--
--   where $q$ is a constant larger than $n$ (p. 409). Let $\mathbf{x}^0 > \mathbf{0}$ and $(\mathbf{p}^0, \mathbf{s}^0)$ with $\mathbf{s}^0 > \mathbf{0}$ be feasible solutions to the primal and dual problem, respectively. Let $\varepsilon > 0$ be the optimality tolerance.
--
--   Any algorithm that maintains primal and dual feasibility and reduces $G(\mathbf{x}, \mathbf{s})$ by an amount greater than or equal to $\delta > 0$ at each iteration finds a solution to the primal and dual problems with duality gap
--
--   $$(\mathbf{s}^K)'\mathbf{x}^K \le \varepsilon,$$
--
--   after
--
--   $$K = \left\lceil \frac{G(\mathbf{x}^0, \mathbf{s}^0) + (q-n)\log(1/\varepsilon) - n\log n}{\delta} \right\rceil$$
--
--   iterations.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 9.4, p. 410 (potential function p. 409, Assumption 9.3 p. 409)

import Definitions.Def_LinearOptimization_LogBarrier_CentralPath
import Definitions.Def_LinearOptimization_InteriorPointPotential


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 9.4 (p. 410).** Potential reduction implies an explicit
iteration bound: if every step keeps `(x^k, s^k)` interior primal-dual
feasible and cuts `G` by at least `δ`, then after
`K = ⌈(G(x⁰, s⁰) + (q − n) log(1/ε) − n log n) / δ⌉` iterations the
duality gap satisfies `(s^K)'x^K ≤ ε`. -/

theorem LinearOptimization.interior_point_potential_reduction {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (q delta eps : ℝ) (hq : (n : ℝ) < q) (hdelta : 0 < delta)
    (heps : 0 < eps)
    (x : ℕ → Fin n → ℝ) (p : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (hfeas : ∀ k, A.mulVec (x k) = b ∧ (∀ j, 0 < x k j) ∧
      Aᵀ.mulVec (p k) + s k = c ∧ (∀ j, 0 < s k j))
    (hdec : ∀ k, interiorPointPotential q (x (k + 1)) (s (k + 1)) ≤
      interiorPointPotential q (x k) (s k) - delta)
    (K : ℕ)
    (hK : K = ⌈(interiorPointPotential q (x 0) (s 0) +
      (q - n) * Real.log (1 / eps) - n * Real.log n) / delta⌉₊) :
    s K ⬝ᵥ x K ≤ eps := by
  sorry
