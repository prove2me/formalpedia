-- Prove2me | Theorems.Thm_HomotopyProxVM_lemma_16
-- name    : HomotopyProxVM.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:39.892023+00:00
-- url     : https://prove2.me/theorems/de988e3b-4f41-4716-a37b-1cfbcc37410f
-- title:
--   Lemma 16, p.24 — one step contracts by $\omega$ towards $x^*_{\tau_{k+1}}$
-- statement:
--   Let $f$ be $\mu_f$-strongly convex and $L_f$-smooth and let $g$ be proper, closed and convex. Let $0<m\le L<+\infty$ with $\omega:=\frac1m\sqrt{(L-2\mu_f)m+L_f^2}<1$, and let $m\mathbb I\preceq H\preceq L\mathbb I$. If $x^+$ is an exact step of (12) from $x$ with metric $H$ and parameter $\tau\in(0,1]$, and $y=x^*_\tau$ solves (8) at $\tau$, then
--
--   $$
--   \|x^+-y\|_2\le\omega\|x-y\|_2 .
--   $$
--
--   Applied along the scheme this is (56): one step contracts the distance to the solution of the current parametrized problem by the factor $\omega$.
--
--   **Formalization Note** $\preceq$ is the Loewner order. The two bounds make $H$ symmetric positive definite.
--
--   Differences from the source:
--   - generalization: the sequence {xᵏ} of (12) with H_k, τ_{k+1} → any point x, any H with mI ⪯ H ⪯ LI, any τ ∈ (0,1], any vector ξ; reason: (56) is the instance x = xᵏ, H = H_k, τ = τ_{k+1}, ξ = ξ⁰
--   - encoding: f : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex, differentiable on dom(f) → f : ℝᵖ → ℝ, differentiable on all of ℝᵖ; reason: Lf-smoothness makes dom(f) open and a Lipschitz gradient with closedness makes it closed, so dom(f) = ℝᵖ and no instance changes
--   - encoding: g : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex → g given by its domain D and its values on D; closed means the epigraph {(x,t) | x ∈ D, g x ≤ t} is closed; prox and argmin are sets of minimizers over D; reason: every proper function ℝᵖ → ℝ ∪ {+∞} has this form and the values off D are never read
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Lemma 16, (56), p.24

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_HomotopyProxVM_IsStronglyConvexParam
import Definitions.Def_HomotopyProxVM_IsSmoothParam
import Definitions.Def_HomotopyProxVM_IsClosedFn
import Definitions.Def_HomotopyProxVM_IsPathSolution
import Definitions.Def_HomotopyProxVM_IsExactStep
import Definitions.Def_HomotopyProxVM_omegaConst

open scoped MatrixOrder

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Lemma 16, (56), p.24: for `f` `μ_f`-strongly convex and `L_f`-smooth, `0 < m ≤ L`,
`ω < 1` and `mI ⪯ H ⪯ LI`, a step of the scheme (12) at `τ` satisfies
`‖x⁺ − x*_τ‖₂ ≤ ω‖x − x*_τ‖₂`.

**Formalization Note.** This is the one-step form: `x`, `H` and `τ ∈ (0,1]` are arbitrary, and (56)
is the instance `x = xᵏ`, `H = H_k`, `τ = τ_{k+1}`. `⪯` is the Loewner order `MatrixOrder`; the
bounds make `H` symmetric positive definite, so `H⁻¹` is the true inverse. -/
theorem lemma_16 {p : ℕ} {f g : EuclideanSpace ℝ (Fin p) → ℝ} {D : Set (EuclideanSpace ℝ (Fin p))}
    {μ Lf m L τ : ℝ} {ξ x xplus y : EuclideanSpace ℝ (Fin p)} {H : Matrix (Fin p) (Fin p) ℝ}
    (hf_sc : IsStronglyConvexParam f μ) (hf_smooth : IsSmoothParam f Lf)
    (hg : OneStepProx.IsProperConvex D g) (hg_closed : IsClosedFn D g)
    (hm : 0 < m) (hmL : m ≤ L) (hω : omegaConst μ Lf m L < 1)
    (hτ : τ ∈ Set.Ioc (0 : ℝ) 1)
    (hH : m • (1 : Matrix (Fin p) (Fin p) ℝ) ≤ H ∧ H ≤ L • (1 : Matrix (Fin p) (Fin p) ℝ))
    (hstep : IsExactStep f D g ξ H τ x xplus)
    (hy : IsPathSolution f D g ξ τ y) :
    ‖xplus - y‖ ≤ omegaConst μ Lf m L * ‖x - y‖ := by sorry

end HomotopyProxVM
