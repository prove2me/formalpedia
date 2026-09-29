-- Prove2me | Theorems.Thm_LinearOptimization_interior_point_path_following_iterations
-- name    : LinearOptimization.interior_point_path_following_iterations
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:46:19.501338+00:00
-- url     : https://prove2.me/theorems/9bc3d78d-1c8c-4172-876d-22e08c95626b
-- title:
--   Iteration bound $O(\sqrt{n}\,\log(n\mu^0/\varepsilon))$ for the primal path following algorithm
-- statement:
--   **(Theorem 9.7, p. 426, GOAL — iteration bound for primal path following)** Assume that the primal path following algorithm uses
--
--   $$\alpha = 1 - \frac{\sqrt{\beta} - \beta}{\sqrt{\beta} + \sqrt{n}},$$
--
--   where $\beta < 1$ [formally $0 < \beta < 1$; see design_note], and starts with an initial primal and dual feasible solution $(\mathbf{x}^0, \mathbf{s}^0, \mathbf{p}^0)$, with $\mathbf{x}^0 > \mathbf{0}$, $\mathbf{s}^0 > \mathbf{0}$, that satisfies
--
--   $$\left\| \frac{1}{\mu^0} X_0 S_0 \mathbf{e} - \mathbf{e} \right\| \le \beta.$$
--
--   Then, after
--
--   $$K = \left\lceil \frac{\sqrt{\beta} + \sqrt{n}}{\sqrt{\beta} - \beta} \, \log \frac{(\mathbf{s}^0)'\mathbf{x}^0 (1+\beta)}{\varepsilon(1-\beta)} \right\rceil$$
--
--   iterations, it finds a primal and dual feasible solution $(\mathbf{x}^K, \mathbf{s}^K, \mathbf{p}^K)$ with duality gap
--
--   $$(\mathbf{s}^K)'\mathbf{x}^K \le \varepsilon.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 9.7, p. 426 (proof pp. 427-429; final display and Eq. (9.23) p. 429)

import Definitions.Def_LinearOptimization_PathFollowing


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 9.7 (p. 426).** Primal path following reaches duality
gap `≤ ε` — primal and dual feasibly — within
`K = ⌈((√β + √n)/(√β − β)) log((s⁰)'x⁰(1+β)/(ε(1−β)))⌉` iterations, when
run with `α = 1 − (√β − β)/(√β + √n)` from a `β`-close interior feasible
start. -/

theorem LinearOptimization.interior_point_path_following_iterations {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (beta eps alpha : ℝ) (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (heps : 0 < eps)
    (halpha : alpha = 1 -
      (Real.sqrt beta - beta) / (Real.sqrt beta + Real.sqrt n))
    (x : ℕ → Fin n → ℝ) (p : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (mu : ℕ → ℝ) (hmu0 : 0 < mu 0)
    (hxfeas0 : A.mulVec (x 0) = b) (hx0 : ∀ j, 0 < x 0 j)
    (hsfeas0 : Aᵀ.mulVec (p 0) + s 0 = c) (hs0 : ∀ j, 0 < s 0 j)
    (hprox0 : centralPathProximity (mu 0) (x 0) (s 0) ≤ beta)
    (hrun : IsPathFollowingRun A c alpha x p s mu)
    (K : ℕ)
    (hK : K = ⌈(Real.sqrt beta + Real.sqrt n) / (Real.sqrt beta - beta) *
      Real.log ((s 0 ⬝ᵥ x 0) * (1 + beta) / (eps * (1 - beta)))⌉₊) :
    A.mulVec (x K) = b ∧ 0 ≤ x K ∧
      Aᵀ.mulVec (p K) + s K = c ∧ 0 ≤ s K ∧
      s K ⬝ᵥ x K ≤ eps := by
  sorry
