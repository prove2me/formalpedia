-- Prove2me | Theorems.Thm_LinearOptimization_ellipsoid_method_correct
-- name    : LinearOptimization.ellipsoid_method_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-06T14:43:12.226919+00:00
-- url     : https://prove2.me/theorems/cabc1b5f-37a0-4206-98a9-c83ff5c4aec7
-- title:
--   Ellipsoid method correctness in $\lceil 2(n+1)\log(V/v)\rceil$ iterations
-- statement:
--   **(Theorem 8.2, p. 372, GOAL — correctness of the ellipsoid method)** Let $P$ be a bounded polyhedron that is either empty or full-dimensional and for which the prior information $\mathbf{x}_0$, $r$, $v$, $V$ is available: $P \subset E_0 = E(\mathbf{x}_0, r^2 I)$, $\mathrm{Vol}(E_0) \le V$, and either $P = \emptyset$ or $\mathrm{Vol}(P) > v$.
--
--   Then the ellipsoid method decides correctly whether $P$ is nonempty or not, i.e., if $\mathbf{x}_{t^*-1} \notin P$ [no center $\mathbf{x}_0, \dots, \mathbf{x}_{t^*-1}$ of an admissible run lies in $P$], then $P$ is empty, where
--
--   $$t^* = \lceil 2(n+1)\log(V/v) \rceil.$$
--
--   Equivalently: if $P$ is nonempty, every admissible run of the ellipsoid method reaches a feasible center $\mathbf{x}_t \in P$ for some $t < t^*$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 8.2, p. 372

import Definitions.Def_LinearOptimization_EllipsoidMethod


open Matrix MeasureTheory

/-- **Bertsimas & Tsitsiklis, Theorem 8.2 (p. 372).** Correctness of the ellipsoid method: if
`P = {x | Ax ≥ b}` is bounded and either empty or full-dimensional,
`P ⊆ E(x₀, r²I)`, `Vol(E(x₀, r²I)) ≤ V`, `Vol(P) > v` unless `P = ∅`,
and an admissible run started at `(x₀, r²I)` has no feasible center
before `t* = ⌈2(n+1) log(V/v)⌉`, then `P` is empty. -/

theorem LinearOptimization.ellipsoid_method_correct {m n : ℕ} (hn : 2 ≤ n)
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x0 : Fin n → ℝ) (r v V : ℝ) (hr : 0 < r) (hv : 0 < v)
    (hbdd : IsBoundedSet (polyhedron A b))
    (hdim : polyhedron A b = ∅ ∨ IsFullDimensional (polyhedron A b))
    (hcover : polyhedron A b ⊆ ellipsoidBall x0 r)
    (hV : volume (ellipsoidBall x0 r) ≤ ENNReal.ofReal V)
    (hvol : polyhedron A b ≠ ∅ →
      ENNReal.ofReal v < volume (polyhedron A b))
    (tstar : ℕ)
    (htstar : tstar = ⌈2 * ((n : ℝ) + 1) * Real.log (V / v)⌉₊)
    (x : ℕ → Fin n → ℝ) (D : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hx0 : x 0 = x0)
    (hD0 : D 0 = r ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ))
    (hrun : IsEllipsoidRun A b x D tstar)
    (hmiss : ∀ t < tstar, x t ∉ polyhedron A b) :
    polyhedron A b = ∅ := by
  sorry
