-- Prove2me | Theorems.Thm_HomotopyProxVM_fixed_point_iff
-- name    : HomotopyProxVM.fixed_point_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:34.693632+00:00
-- url     : https://prove2.me/theorems/5b3f6b77-bc18-4c17-bf65-56601a491b3b
-- title:
--   (10), p.7 — solutions of (8) are exactly the fixed points
-- statement:
--   Let $g$ be proper, closed and convex, let $f$ be proper, closed and convex with an open domain on which it is differentiable, let $H$ be symmetric positive definite, and let $\tau\in(0,1]$. A point $y\in\operatorname{dom}(f)$ solves (8) if and only if
--
--   $$
--   y=\operatorname{prox}^H_{\frac1\tau g}\Bigl(y-H^{-1}\bigl(\nabla f(y)-(\tfrac1\tau-1)\xi^0\bigr)\Bigr).
--   $$
--
--   In the convergence proof this is applied with the metric $H_k$ and $\tau=\tau_{k+1}$, which lets a step of (12) and the point $x^*_{\tau_{k+1}}$ be compared through the nonexpansiveness of the same operator.
--
--   **Formalization Note** The fixed-point equation is the statement that $y$ belongs to the set of minimizers defining the prox.
--
--   Differences from the source:
--   - reading: f : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex, with ∇f used at the points of (9) without saying where f is differentiable → f given by an open convex domain U = dom(f) and its values on U, convex and differentiable on U, closed as a closed epigraph; (8) minimizes F_τ over U ∩ dom(g); reason: (9) needs ∇f at x*_τ, and every f of the paper is differentiable on an open dom(f) (L_f-smooth f on ℝᵖ, §2.1; self-concordant f ∈ C³(dom f), Definition 12); U = ℝᵖ is the case of Assumption 2
--   - encoding: g : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex → g given by its domain D and its values on D; closed means the epigraph {(x,t) | x ∈ D, g x ≤ t} is closed; prox and argmin are sets of minimizers over D; reason: every proper function ℝᵖ → ℝ ∪ {+∞} has this form and the values off D are never read
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §3.2, (10), p.7

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_HomotopyProxVM_IsClosedFn
import Definitions.Def_HomotopyProxVM_IsPathSolution
import Definitions.Def_HomotopyProxVM_IsExactStep

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §3.2, (10), p.7: for any `H ∈ 𝕊ᵖ₊₊` and `τ ∈ (0,1]`, a point `y ∈ dom(f)` solves (8) if and only if
`y` is a fixed point, `y = prox^H_{(1/τ) g}( y − H⁻¹( ∇f(y) − (1/τ − 1) ξ⁰ ) )`.

**Formalization Note.** `f` is encoded by its effective domain `U`, an open convex set on which `f` is
finite, convex and differentiable, with "closed" a closed epigraph; `g` by its domain `D` and its
values on `D`. Problem (8) is the minimization of `F_τ` over `U ∩ D`. The fixed-point equation is
`IsExactStep f D g ξ H τ y y`, membership in the set of minimizers defining the prox. -/
theorem fixed_point_iff {p : ℕ} {f g : EuclideanSpace ℝ (Fin p) → ℝ}
    {U D : Set (EuclideanSpace ℝ (Fin p))} {H : Matrix (Fin p) (Fin p) ℝ}
    {τ : ℝ} (ξ : EuclideanSpace ℝ (Fin p))
    (hU : IsOpen U) (hf_cvx : ConvexOn ℝ U f) (hf_diff : DifferentiableOn ℝ f U)
    (hf_closed : IsClosedFn U f)
    (hg : OneStepProx.IsProperConvex D g) (hg_closed : IsClosedFn D g)
    (hH : H.PosDef) (hτ : τ ∈ Set.Ioc (0 : ℝ) 1) (y : EuclideanSpace ℝ (Fin p)) (hy : y ∈ U) :
    IsPathSolution f (U ∩ D) g ξ τ y ↔ IsExactStep f D g ξ H τ y y := by sorry

end HomotopyProxVM
