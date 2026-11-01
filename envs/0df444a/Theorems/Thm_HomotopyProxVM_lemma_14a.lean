-- Prove2me | Theorems.Thm_HomotopyProxVM_lemma_14a
-- name    : HomotopyProxVM.lemma_14a
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:41.979457+00:00
-- url     : https://prove2.me/theorems/b762720f-e77b-4191-8e00-bdcb91f4c3e9
-- title:
--   Lemma 14(a), pp.22–23 — distances along the homotopy path (corrected: the middle link of (51) is dropped)
-- statement:
--   Let $f$ be proper, closed and $\mu_f$-strongly convex with an open domain on which it is differentiable, and let $g$ be proper, closed, convex and $L_g$-Lipschitz on $\operatorname{dom}(g)$. Let $x^0\in\operatorname{dom}(f)\cap\operatorname{dom}(g)$ and $\xi^0\in\partial g(x^0)$. Let $x^*_\tau,x^*_{\hat\tau}\in\operatorname{dom}(f)$ be solutions of (9) at $\tau,\hat\tau\in(0,1]$. Then
--
--   $$
--   \|x^0-x^*_\tau\|_2\le\frac{\|\nabla f(x^0)+\xi^0\|_2}{\mu_f},
--   $$
--
--   $$
--   \|x^*_\tau-x^*_{\hat\tau}\|_2\le\frac{|\tau-\hat\tau|}{\hat\tau\mu_f}\|\nabla f(x^*_\tau)+\xi^0\|_2,
--   \qquad
--   \|x^*_\tau-x^*_{\hat\tau}\|_2\le\frac{|\tau-\hat\tau|}{\tau\hat\tau\mu_f}\bigl(L_g+\|\xi^0\|_2\bigr).
--   $$
--
--   These bounds say that the homotopy path is Lipschitz in $1/\tau$ and starts within a controlled distance of $x^0$; they drive both the recursion (62) and the final bound of Theorem 4.
--
--   Differences from the source:
--   - correction: ‖x*_τ − x*_τ̂‖₂ ≤ (|τ−τ̂|/(τ̂μ_f))‖∇f(x*_τ)+ξ⁰‖₂ ≤ (|τ−τ̂|/(ττ̂μ_f))(L_g+‖ξ⁰‖₂), a chain → the two outer inequalities, stated separately, without the middle link; reason: the middle link is false when dom(g) ≠ ℝᵖ: f(x) = (x−5)²/2, g the indicator of [−1,1], x⁰ = ξ⁰ = 0, L_g = 0, τ = 1, τ̂ = 1/2 gives x*_τ = x*_τ̂ = 1 and reads 4 ≤ 0. The outer bound is true: add the two subgradient inequalities divided by τ and τ̂ and use the Lipschitz bound on g(v) − g(u)
--   - reading: f : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex, with ∇f used at the points of (9) without saying where f is differentiable → f given by an open convex domain U = dom(f) and its values on U, convex and differentiable on U, closed as a closed epigraph; (8) minimizes F_τ over U ∩ dom(g); reason: (9) needs ∇f at x*_τ, and every f of the paper is differentiable on an open dom(f) (L_f-smooth f on ℝᵖ, §2.1; self-concordant f ∈ C³(dom f), Definition 12); U = ℝᵖ is the case of Assumption 2
--   - encoding: g : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex → g given by its domain D and its values on D; closed means the epigraph {(x,t) | x ∈ D, g x ≤ t} is closed; prox and argmin are sets of minimizers over D; reason: every proper function ℝᵖ → ℝ ∪ {+∞} has this form and the values off D are never read
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Lemma 14(a), (51), pp.22–23

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_HomotopyProxVM_IsClosedFn
import Definitions.Def_HomotopyProxVM_IsLipschitzOnDom

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Lemma 14(a), (51), pp.22–23, **corrected**: for `x⁰ ∈ dom(F)`, `ξ⁰ ∈ ∂g(x⁰)`,
`f` `μ_f`-strongly convex and `x*_τ`, `x*_τ̂` solutions of (9) at `τ, τ̂ ∈ (0,1]`,
`‖x⁰ − x*_τ‖₂ ≤ ‖∇f(x⁰) + ξ⁰‖₂/μ_f`,
`‖x*_τ − x*_τ̂‖₂ ≤ (|τ − τ̂|/(τ̂ μ_f)) ‖∇f(x*_τ) + ξ⁰‖₂`, and
`‖x*_τ − x*_τ̂‖₂ ≤ (|τ − τ̂|/(τ τ̂ μ_f)) (L_g + ‖ξ⁰‖₂)`.

**Formalization Note.** `f` is encoded by its effective domain `U`, an open convex set on which `f` is
finite and differentiable (so that `∇f` in (9) and (51) exists), with "closed" a closed epigraph;
`μ_f`-strong convexity is "`f − (μ_f/2)‖·‖²` convex on `U`" with `μ_f > 0`. `g` is encoded by its
domain `D` and its values on `D`. A solution of (9) at `τ` is a point `u ∈ U` with
`−(τ∇f(u) − (1 − τ)ξ⁰) ∈ ∂g(u)`, the published subgradient relative to `D`.
(51) prints the last two as a chain `… ≤ (|τ−τ̂|/(τ̂μ_f))‖∇f(x*_τ)+ξ⁰‖₂ ≤
(|τ−τ̂|/(ττ̂μ_f))(L_g+‖ξ⁰‖₂)`. The middle link is false when `dom(g) ≠ ℝᵖ`: for `f(x) = (x−5)²/2`, `g`
the indicator of `[−1,1]`, `x⁰ = ξ⁰ = 0`, `L_g = 0`, `τ = 1`, `τ̂ = 1/2`, it reads `4 ≤ 0`. Both
outer inequalities are true and are stated. -/
theorem lemma_14a {p : ℕ} {f g : EuclideanSpace ℝ (Fin p) → ℝ}
    {U D : Set (EuclideanSpace ℝ (Fin p))}
    {μ Lg τ τhat : ℝ} {x₀ ξ u v : EuclideanSpace ℝ (Fin p)}
    (hU : IsOpen U) (hf_sc : 0 < μ ∧ ConvexOn ℝ U (fun x => f x - μ / 2 * ‖x‖ ^ 2))
    (hf_diff : DifferentiableOn ℝ f U) (hf_closed : IsClosedFn U f)
    (hg : OneStepProx.IsProperConvex D g) (hg_closed : IsClosedFn D g)
    (hg_lip : IsLipschitzOnDom D g Lg)
    (hx₀ : x₀ ∈ U) (hξ : BubeckCO.PSGD.IsSubgradient D g x₀ ξ)
    (hτ : τ ∈ Set.Ioc (0 : ℝ) 1) (hτhat : τhat ∈ Set.Ioc (0 : ℝ) 1)
    (hu : u ∈ U ∧ BubeckCO.PSGD.IsSubgradient D g u (-(τ • gradient f u - (1 - τ) • ξ)))
    (hv : v ∈ U ∧ BubeckCO.PSGD.IsSubgradient D g v (-(τhat • gradient f v - (1 - τhat) • ξ))) :
    ‖x₀ - u‖ ≤ ‖gradient f x₀ + ξ‖ / μ ∧
    ‖u - v‖ ≤ |τ - τhat| / (τhat * μ) * ‖gradient f u + ξ‖ ∧
    ‖u - v‖ ≤ |τ - τhat| / (τ * τhat * μ) * (Lg + ‖ξ‖) := by sorry

end HomotopyProxVM
