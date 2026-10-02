-- Prove2me | Theorems.Thm_HunterPDE_Friedrichs_smooth_solution_unique
-- name    : HunterPDE.Friedrichs.smooth_solution_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:56:54.259471+00:00
-- url     : https://prove2.me/theorems/ecb0b263-2f26-42bc-820d-c6af2f506ee2
-- title:
--   Corollary 8.7 — uniqueness of smooth solutions u ∈ C¹(Ω̄) of (8.1)
-- statement:
--   Under the hypotheses of Theorem 8.6 (smooth BVP, non-characteristic boundary, positive symmetric with constant $c>0$, maximally positive boundary condition), a smooth solution of (8.1) is unique: if $u_1, u_2 \in C^1(\overline\Omega;\mathbb{R}^m)$ both satisfy
--   $$Lu_k = f \ \text{ pointwise in } \Omega, \qquad B_- u_k = 0 \ \text{ on } \partial\Omega \qquad (k = 1,2),$$
--   then $u_1 = u_2$ on $\overline\Omega$.
--
--   **Formalization Note.** $C^1(\overline\Omega)$ functions are modelled as $C^1$ functions on $\mathbb{R}^n$; the conclusion is equality at every point of `closure Ω`. The right-hand side $f$ is an arbitrary function (the solutions are classical).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 226, Corollary 8.7

import Mathlib
import Definitions.Def_HunterPDE_Friedrichs_BoundaryValueProblem

open MeasureTheory Matrix

namespace HunterPDE.Friedrichs

/-- Hunter, *Notes on PDEs* (revised 6/18/2014), Corollary 8.7, p. 226. Under the smoothness
conditions of Definition 8.1, a non-characteristic boundary (§8.2), the positivity condition of
Definition 8.4 (constant `c`) and a maximally positive boundary condition (Definition 8.5), a
smooth solution `u ∈ C¹(Ω̄)` of (8.1) — `Lu = f` pointwise in `Ω` and `B₋u = 0` on `∂Ω` — is
unique: two such solutions with the same `f` agree on `Ω̄`. -/
theorem smooth_solution_unique {n m : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (A : Fin n → EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ)
    (C Bm : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin m) ℝ) (c : ℝ)
    (hsmooth : IsSmoothBVP Ω A C Bm) (hnc : IsNoncharacteristic Ω A)
    (hpos : IsPositiveSymmetric Ω A C c) (hmax : IsMaximallyPositive Ω A Bm)
    (f u₁ u₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hu₁ : u₁ ∈ Dom Ω Bm) (hu₂ : u₂ ∈ Dom Ω Bm)
    (hL₁ : ∀ x ∈ Ω, Lop A C u₁ x = f x) (hL₂ : ∀ x ∈ Ω, Lop A C u₂ x = f x) :
    ∀ x ∈ closure Ω, u₁ x = u₂ x := by sorry

end HunterPDE.Friedrichs
