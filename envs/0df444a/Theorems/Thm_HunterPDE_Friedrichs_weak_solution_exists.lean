-- Prove2me | Theorems.Thm_HunterPDE_Friedrichs_weak_solution_exists
-- name    : HunterPDE.Friedrichs.weak_solution_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:57:43.541126+00:00
-- url     : https://prove2.me/theorems/a29e96dd-6feb-48da-82d4-b8ecfe9b408d
-- title:
--   Theorem 8.9 — existence of a weak solution u ∈ L²(Ω) of (8.1) for every f ∈ L²(Ω)
-- statement:
--   Under the hypotheses of Theorem 8.6 (smooth BVP, non-characteristic boundary, positive symmetric with constant $c>0$, maximally positive boundary condition), for every $f \in L^2(\Omega;\mathbb{R}^m)$ there exists $u \in L^2(\Omega;\mathbb{R}^m)$ with
--   $$\int_\Omega u^T L^* v\,dx = \int_\Omega f^T v\,dx \qquad \text{for all } v \in D^* = \{v \in C^1(\overline\Omega) : B_+^T v = 0 \text{ on } \partial\Omega\},$$
--   i.e. a weak solution in the sense of Definition 8.8. The test functions are not compactly supported, so the boundary condition $B_-u = 0$ is imposed weakly through the adjoint condition $B_+^Tv = 0$.
--
--   **Formalization Note.** $f \in L^2(\Omega)$ is `MemLp f 2 (volume.restrict Ω)`; the solution's membership in $L^2(\Omega)$ is part of `IsWeakSolution`.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 226, Theorem 8.9

import Mathlib
import Definitions.Def_HunterPDE_Friedrichs_BoundaryValueProblem

open MeasureTheory Matrix

namespace HunterPDE.Friedrichs

/-- Hunter, *Notes on PDEs* (revised 6/18/2014), Theorem 8.9, p. 226. Under the smoothness
conditions of Definition 8.1, a non-characteristic boundary (§8.2), the positivity condition of
Definition 8.4 (constant `c`) and a maximally positive boundary condition (Definition 8.5), for
every `f ∈ L²(Ω; ℝᵐ)` there is a weak solution `u ∈ L²(Ω; ℝᵐ)` of (8.1) in the sense of
Definition 8.8. -/
theorem weak_solution_exists {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hsmooth : IsSmoothBVP Ω A C Bm) (hnc : IsNoncharacteristic Ω A)
    (hpos : IsPositiveSymmetric Ω A C c) (hmax : IsMaximallyPositive Ω A Bm)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : MemLp f 2 (volume.restrict Ω)) :
    ∃ u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
      IsWeakSolution Ω A C Bm f u := by sorry

end HunterPDE.Friedrichs
