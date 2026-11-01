-- Prove2me | Theorems.Thm_HomotopyProxVM_path_solution
-- name    : HomotopyProxVM.path_solution
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:36.203484+00:00
-- url     : https://prove2.me/theorems/84cd8d98-7556-4a8a-ac94-f850dccfff0c
-- title:
--   (8)–(9), p.6 — $x^*_\tau$ exists, is unique and is characterized by (9)
-- statement:
--   Let $g$ be proper, closed and convex, let $f$ be proper, closed and convex with an open domain $\operatorname{dom}(f)$ on which it is differentiable, and let $\xi^0\in\mathbb R^p$. Problem (8) minimizes $F_\tau$ over $\operatorname{dom}(f)\cap\operatorname{dom}(g)$.
--
--   1. For every $\tau\in[0,1]$, a point $y\in\operatorname{dom}(f)$ solves (8) if and only if
--
--   $$
--   0\in\tau\nabla f(y)-(1-\tau)\xi^0+\partial g(y).
--   $$
--
--   2. If $f$ is strongly convex and $\operatorname{dom}(f)\cap\operatorname{dom}(g)\ne\emptyset$, then for every $\tau\in(0,1]$ the problem (8) has exactly one solution.
--
--   3. If $x^0\in\operatorname{dom}(f)$ and $\xi^0\in\partial g(x^0)$, then $x^0$ solves (8) at $\tau=0$.
--
--   This is the parametric optimality condition on which the whole homotopy rests.
--
--   **Formalization Note** The inclusion is written $-(\tau\nabla f(y)-(1-\tau)\xi^0)\in\partial g(y)$, with the published subgradient relative to the domain of $g$, which includes $y\in\operatorname{dom}(g)$.
--
--   Differences from the source:
--   - reading: f : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex, with ∇f used at the points of (9) without saying where f is differentiable → f given by an open convex domain U = dom(f) and its values on U, convex and differentiable on U, closed as a closed epigraph; (8) minimizes F_τ over U ∩ dom(g); reason: (9) needs ∇f at x*_τ, and every f of the paper is differentiable on an open dom(f) (L_f-smooth f on ℝᵖ, §2.1; self-concordant f ∈ C³(dom f), Definition 12); U = ℝᵖ is the case of Assumption 2
--   - encoding: g : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex → g given by its domain D and its values on D; closed means the epigraph {(x,t) | x ∈ D, g x ≤ t} is closed; prox and argmin are sets of minimizers over D; reason: every proper function ℝᵖ → ℝ ∪ {+∞} has this form and the values off D are never read
--   - reading: x*_τ := argmin F_τ for τ ∈ [0,1], with "we can choose x*₀ = x⁰" at τ = 0 → exists and is unique for f strongly convex and τ ∈ (0,1]; x⁰ is a solution at τ = 0; reason: the page's argmin is claimed as a single point but its existence for merely convex f is not implied by anything on the page (it needs the strong convexity of Assumption 2), and at τ = 0 solutions need not be unique, which is why the page says "choose"
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, §3.1, (8)–(9) and the case τ = 0, p.6

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_HomotopyProxVM_IsClosedFn
import Definitions.Def_HomotopyProxVM_IsPathSolution

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, §3.1, (8)–(9), p.6: `x*_τ` is characterized by the parametric optimality condition
`0 ∈ τ∇f(x*_τ) − (1 − τ)ξ⁰ + ∂g(x*_τ)`, "necessary and sufficient for `x*_τ` to be an optimal
solution of (8)", for every `τ ∈ [0,1]`; for `f` strongly convex and `τ ∈ (0,1]` the solution exists
and is unique; and at `τ = 0`, for `ξ⁰ ∈ ∂g(x⁰)`, one can choose `x*₀ = x⁰`.

**Formalization Note.** `f` is encoded by its effective domain `U`, an open convex set on which `f` is
finite, convex and differentiable (so that `∇f` in (9) exists), with "closed" a closed epigraph
`IsClosedFn U f`; `g` is encoded by its domain `D` and its values on `D`. Problem (8) is the
minimization of `F_τ` over `dom(F_τ) = U ∩ D`. `0 ∈ v + ∂g(y)` is written `−v ∈ ∂g(y)`, with the
published subgradient relative to `D`. Strong convexity is the paper's "`f − (μ/2)‖·‖²` convex" on
`dom(f) = U`, with `μ > 0`; existence uses `dom(F) ≠ ∅` (Assumption 1). The vector `ξ` is arbitrary in
the first two parts: they do not use `ξ ∈ ∂g(x⁰)`. -/
theorem path_solution {p : ℕ} {f g : EuclideanSpace ℝ (Fin p) → ℝ}
    {U D : Set (EuclideanSpace ℝ (Fin p))} (ξ : EuclideanSpace ℝ (Fin p))
    (hU : IsOpen U) (hf_cvx : ConvexOn ℝ U f) (hf_diff : DifferentiableOn ℝ f U)
    (hf_closed : IsClosedFn U f)
    (hg : OneStepProx.IsProperConvex D g) (hg_closed : IsClosedFn D g) :
    (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ U, IsPathSolution f (U ∩ D) g ξ τ y ↔
      BubeckCO.PSGD.IsSubgradient D g y (-(τ • gradient f y - (1 - τ) • ξ))) ∧
    (∀ μ : ℝ, 0 < μ → ConvexOn ℝ U (fun x => f x - μ / 2 * ‖x‖ ^ 2) → (U ∩ D).Nonempty →
      ∀ τ ∈ Set.Ioc (0 : ℝ) 1, ∃! y, IsPathSolution f (U ∩ D) g ξ τ y) ∧
    (∀ x₀ ∈ U, BubeckCO.PSGD.IsSubgradient D g x₀ ξ → IsPathSolution f (U ∩ D) g ξ 0 x₀) := by sorry

end HomotopyProxVM
