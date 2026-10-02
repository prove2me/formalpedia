-- Prove2me | Theorems.Thm_NumStochOpt_Bounds_property_b_recourse_piecewise_linear_convex_in_hT
-- name    : NumStochOpt.Bounds.property_b_recourse_piecewise_linear_convex_in_hT
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:58:07.146097+00:00
-- url     : https://prove2.me/theorems/99eba51c-cf7b-4389-b4d9-c6e180fad386
-- title:
--   Property (b) — $(h,T)\mapsto Q(x,(q,h,T))$ is piecewise linear and convex
-- statement:
--   Let $W$ be an $m_2\times n_2$ recourse matrix with complete recourse ($\{Wy:y\ge0\}=\mathbb R^{m_2}$), and let the cost vector $q\in\mathbb R^{n_2}$ be dual feasible (some $u$ satisfies $W^Tu\le q$). Fix a first-stage decision $x\in\mathbb R^{n_1}$. Then the recourse cost
--   $$
--   (h,T)\;\longmapsto\;Q(x,\xi=(q,h,T))=\min\{q^Ty : Wy=h-Tx,\ y\ge0\}
--   $$
--   is finite, convex and piecewise linear on $\mathbb R^{m_2}\times\mathbb R^{m_2\times n_1}$: there are finitely many affine functions $g_1,\dots,g_K$ of $(h,T)$, $K\ge1$, with
--   $$
--   Q(x,(q,h,T))=\max_{1\le k\le K} g_k(h,T)\qquad\text{for all } h,T .
--   $$
--
--   This is what makes $Q(x,\cdot)$ convex in the random data when $q$ is deterministic, the hypothesis of both the Jensen lower bound (2.26) and the Edmundson–Madansky upper bound (2.33).
--
--   **Formalization Note** The book states (b) for $x\in K=K_1\cap K_2$ under its standing assumptions of dual feasibility (p. 39) and complete recourse (p. 40). Under complete recourse $K_2=\mathbb R^{n_1}$, and the statement is made for every $x$. "Convex and piecewise linear" is rendered as "a maximum of finitely many affine functions", which is equivalent for a finite function on the whole space; equality with a real number also records that $Q$ is finite.
-- source:
--   P. Kall, A. Ruszczyński, K. Frauendorfer, "Approximation Techniques in Stochastic Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 2, p. 40, property (b) (standing assumptions pp. 39-40)

import Mathlib
import Definitions.Def_NumStochOpt_Bounds_RecourseCost

open Matrix

namespace NumStochOpt.Bounds

/-- Property (b), p. 40: under complete recourse and dual feasibility of `q`, for every fixed
first-stage decision `x` the map `(h, T) ↦ Q(x, ξ = (q, h, T))` is finite, convex and piecewise
linear, i.e. the pointwise maximum of finitely many affine functions of `(h, T)`. -/
theorem property_b_recourse_piecewise_linear_convex_in_hT {ι κ ν : Type*} [Fintype ι] [Fintype κ]
    [Fintype ν] (W : Matrix ι κ ℝ) (hW : CompleteRecourse W) (q : κ → ℝ) (hq : DualFeasible W q)
    (x : ν → ℝ) :
    ∃ U : Finset ((ι → ℝ) × Matrix ι ν ℝ →ᵃ[ℝ] ℝ), ∃ hU : U.Nonempty,
      ∀ (h : ι → ℝ) (T : Matrix ι ν ℝ),
        recourseCost W q h T x = ((U.sup' hU fun g => g (h, T) : ℝ) : EReal) := by sorry

end NumStochOpt.Bounds
