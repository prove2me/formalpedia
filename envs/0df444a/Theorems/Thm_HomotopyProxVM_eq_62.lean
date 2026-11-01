-- Prove2me | Theorems.Thm_HomotopyProxVM_eq_62
-- name    : HomotopyProxVM.eq_62
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:37:45.236607+00:00
-- url     : https://prove2.me/theorems/01b55af3-deda-4ee5-ba1b-96cbf8a2d8e2
-- title:
--   (62), p.26 — the one-step recursion
-- statement:
--   Under Assumption 2, with $g$ proper, closed and convex, $\xi^0\in\partial g(x^0)$, $0<m\le L$, $\omega<1$ and $m\mathbb I\preceq H_k\preceq L\mathbb I$, let $\tau_k,\tau_{k+1}\in(0,1]$ and let $x^{k+1}$ be the exact step of (12) from $x^k$ with $H_k$ and $\tau_{k+1}$. Then, with $\Delta\tau_k:=|\tau_{k+1}-\tau_k|$,
--
--   $$
--   \|x^{k+1}-x^*_{\tau_{k+1}}\|_2\le\omega\|x^k-x^*_{\tau_k}\|_2+\omega\bigl(L_g+\|\xi^0\|_2\bigr)\frac{\Delta\tau_k}{\mu_f\tau_k\tau_{k+1}} .
--   $$
--
--   The first term is the contraction and the second is the price of moving the target from $x^*_{\tau_k}$ to $x^*_{\tau_{k+1}}$; the update of $\tau_k$ in (19) is designed around this inequality.
--
--   Differences from the source:
--   - generalization: the sequence {xᵏ} of (12), with Algorithm 1's 0 < τ_k < τ_{k+1} ≤ 1 → any x, any H with mI ⪯ H ⪯ LI, any τ, τ⁺ ∈ (0,1]; reason: (62) is the instance along the run
--   - encoding: f : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex, differentiable on dom(f) → f : ℝᵖ → ℝ, differentiable on all of ℝᵖ; reason: Lf-smoothness makes dom(f) open and a Lipschitz gradient with closedness makes it closed, so dom(f) = ℝᵖ and no instance changes
--   - encoding: g : ℝᵖ → ℝ ∪ {+∞} proper, closed, convex → g given by its domain D and its values on D; closed means the epigraph {(x,t) | x ∈ D, g x ≤ t} is closed; prox and argmin are sets of minimizers over D; reason: every proper function ℝᵖ → ℝ ∪ {+∞} has this form and the values off D are never read
-- source:
--   Tran-Dinh, Liang & Toh, A New Homotopy Proximal Variable-Metric Framework for Composite Convex Minimization, arXiv:1812.05243v1, Appendix B.1, display (62), p.26

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
import Definitions.Def_HomotopyProxVM_IsStronglyConvexParam
import Definitions.Def_HomotopyProxVM_IsSmoothParam
import Definitions.Def_HomotopyProxVM_IsClosedFn
import Definitions.Def_HomotopyProxVM_IsLipschitzOnDom
import Definitions.Def_HomotopyProxVM_IsPathSolution
import Definitions.Def_HomotopyProxVM_IsExactStep
import Definitions.Def_HomotopyProxVM_omegaConst

open scoped MatrixOrder

namespace HomotopyProxVM

/-- Tran-Dinh, Liang & Toh, arXiv:1812.05243v1, Appendix B.1, display (62), p.26: the one-step recursion
`‖xᵏ⁺¹ − x*_{τ_{k+1}}‖₂ ≤ ω‖xᵏ − x*_{τ_k}‖₂ + ω(L_g + ‖ξ⁰‖₂) Δτ_k/(μ_f τ_k τ_{k+1})`, with
`Δτ_k := |τ_{k+1} − τ_k|`.

**Formalization Note.** One-step form: `xᵏ = x`, `xᵏ⁺¹ = xplus`, `H_k = H`, `τ_k = τ`,
`τ_{k+1} = τplus`, `x*_{τ_k} = y`, `x*_{τ_{k+1}} = yplus`. -/
theorem eq_62 {p : ℕ} {f g : EuclideanSpace ℝ (Fin p) → ℝ} {D : Set (EuclideanSpace ℝ (Fin p))}
    {μ Lf Lg m L τ τplus : ℝ} {x₀ ξ x xplus y yplus : EuclideanSpace ℝ (Fin p)} {H : Matrix (Fin p) (Fin p) ℝ}
    (hf_sc : IsStronglyConvexParam f μ) (hf_smooth : IsSmoothParam f Lf)
    (hg : OneStepProx.IsProperConvex D g) (hg_closed : IsClosedFn D g)
    (hg_lip : IsLipschitzOnDom D g Lg)
    (hξ : BubeckCO.PSGD.IsSubgradient D g x₀ ξ)
    (hm : 0 < m) (hmL : m ≤ L) (hω : omegaConst μ Lf m L < 1)
    (hτ : τ ∈ Set.Ioc (0 : ℝ) 1) (hτplus : τplus ∈ Set.Ioc (0 : ℝ) 1)
    (hH : m • (1 : Matrix (Fin p) (Fin p) ℝ) ≤ H ∧ H ≤ L • (1 : Matrix (Fin p) (Fin p) ℝ))
    (hstep : IsExactStep f D g ξ H τplus x xplus)
    (hy : IsPathSolution f D g ξ τ y) (hyplus : IsPathSolution f D g ξ τplus yplus) :
    ‖xplus - yplus‖ ≤ omegaConst μ Lf m L * ‖x - y‖ +
      omegaConst μ Lf m L * (Lg + ‖ξ‖) * (|τplus - τ| / (μ * τ * τplus)) := by sorry

end HomotopyProxVM
