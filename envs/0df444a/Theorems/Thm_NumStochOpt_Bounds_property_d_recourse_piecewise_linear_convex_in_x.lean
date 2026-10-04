-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_property_d_recourse_piecewise_linear_convex_in_x
-- name    : NumStochOpt.Bounds.property_d_recourse_piecewise_linear_convex_in_x
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T19:01:23.091627+00:00
-- url     : https://prove2.me/theorems/cfae6293-e5cf-408d-8528-5e9af8b39e93
-- title:
--   Property (d) — $x\mapsto Q(x,\xi)$ is convex piecewise linear
-- statement:
--   Let $W$ have complete recourse and let $q$ be dual feasible ($W^Tu\le q$ for some $u$). Fix $\xi=(q,h,T)$. Then
--   $$
--   x\;\longmapsto\;Q(x,\xi)=\min\{q^Ty : Wy=h-Tx,\ y\ge0\}
--   $$
--   is a finite, convex, piecewise linear function of $x\in\mathbb R^{n_1}$: there are finitely many affine functions $g_1,\dots,g_K$ of $x$, $K\ge1$, with
--   $$
--   Q(x,\xi)=\max_{1\le k\le K} g_k(x)\qquad\text{for all } x .
--   $$
--
--   Convexity in $x$ is what makes the first-stage problem (2.11) and its discretization (2.18) convex programs.
--
--   **Formalization Note** The book states (d) on $K=K_1\cap K_2$; under the standing complete-recourse assumption $K_2=\mathbb R^{n_1}$, and the statement is made on all of $\mathbb R^{n_1}$, which contains $K$. "Convex piecewise linear" is rendered as a maximum of finitely many affine functions.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 40, property (d) (standing assumptions pp. 39-40)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost

open Matrix

namespace NumStochOpt.Bounds

/-- Property (d), p. 40: under complete recourse and dual feasibility of `q`, for every fixed
`ξ = (q, h, T)` the map `x ↦ Q(x, ξ)` is finite, convex and piecewise linear, i.e. the pointwise
maximum of finitely many affine functions of `x`. -/
theorem property_d_recourse_piecewise_linear_convex_in_x {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [Fintype ν] (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ) (hq : DualFeasible W q)
    (h : ι → ℝ) (T : Matrix ι ν ℝ) :
    ∃ U : Finset ((ν → ℝ) →ᵃ[ℝ] ℝ), ∃ hU : U.Nonempty,
      ∀ x : ν → ℝ, recourseCost W q h T x = ((U.sup' hU fun g => g x : ℝ) : EReal) := by sorry

end NumStochOpt.Bounds
