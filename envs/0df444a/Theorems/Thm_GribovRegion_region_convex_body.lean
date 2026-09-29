-- Prove2me | Theorems.Thm_GribovRegion_region_convex_body
-- name    : GribovRegion.region_convex_body
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:28:37.663599+00:00
-- url     : https://prove2.me/theorems/1144d289-c423-4e90-9f23-8fd92900245b
-- title:
--   Geometry of the Gribov region: a bounded convex set containing the origin
-- statement:
--   The geometric properties of the Gribov region collected on p. 189 of the review, in the finite-dimensional model: assuming that distinct configurations give distinct field-dependent parts of the Faddeev--Popov operator,
--
--   1. the perturbative configuration $A = 0$ lies in $\Omega$;
--   2. $\Omega$ is convex;
--   3. $\Omega$ is bounded in every direction: for every $A \neq 0$ there is $\lambda_0 > 0$ with $\lambda A \notin \Omega$ for all $\lambda \ge \lambda_0$;
--   4. $\Omega$ is a bounded subset of the configuration space.
--
--   Together these say that $\Omega$ is a bounded convex neighbourhood of the perturbative point --- the geometric input of Gribov's confinement scenario.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

theorem region_convex_body {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {n : ℕ} (m : FPModel V n)
    (hinj : Function.Injective m.lin) :
    (0 : V) ∈ region m ∧
      Convex ℝ (region m) ∧
      (∀ A : V, A ≠ 0 → ∃ l₀ : ℝ, 0 < l₀ ∧ ∀ l : ℝ, l₀ ≤ l → l • A ∉ region m) ∧
      Bornology.IsBounded (region m) := by sorry

end GribovRegion
