-- Prove2me | Theorems.Thm_LinearMap_exact_dualMap_of_exact
-- name    : LinearMap.exact_dualMap_of_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/e04cb9de-6912-54f4-a85e-68be1baf8308
-- title:
--   Duality preserves exactness of linear maps over a field
-- statement:
--   Let $K$ be a field and let $V_1, V_2, V_3$ be $K$-vector spaces (additive commutative groups with $K$-module structures). Let $f \colon V_1 \to V_2$ and $g \colon V_2 \to V_3$ be $K$-linear maps, and assume the pair is exact at $V_2$ in the sense of `Function.Exact f g`, i.e. for every $x \in V_2$ one has $g(x) = 0$ if and only if $x$ lies in the image of $f$. The conclusion is `Function.Exact g.dualMap f.dualMap`: the transposed pair $$V_3^\vee \xrightarrow{\,g^\vee\,} V_2^\vee \xrightarrow{\,f^\vee\,} V_1^\vee,$$ where $g^\vee$ and $f^\vee$ denote precomposition with $g$ and with $f$ on $K$-linear functionals, is exact at $V_2^\vee$; concretely, a functional $\psi \colon V_2 \to K$ satisfies $\psi \circ f = 0$ if and only if $\psi = \chi \circ g$ for some functional $\chi \colon V_3 \to K$. No finiteness hypothesis on the dimensions is imposed.
--
--   This is the exactness of linear duality over a field at the middle term, the statement needed to dualise an exact sequence of coefficient modules; Mathlib supplies the two end cases (the dual of an injection is surjective and the dual of a surjection is injective) and the identity expressing the image of a dual map as an annihilator. It is used in the construction of dual twists of representations and in the proof that the comparison map $\theta$ attached to a short exact sequence of group-cohomology coefficients is bijective, as cited by [`Rep.exists_dualTwist_shortExact`](thm.html#Rep.exists_dualTwist_shortExact) and [`groupCohomology.bijective_theta_of_shortExact`](thm.html#groupCohomology.bijective_theta_of_shortExact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exact_dualMap_of_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.exact_dualMap_of_exact {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap := by sorry
