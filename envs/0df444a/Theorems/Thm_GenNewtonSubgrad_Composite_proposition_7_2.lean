-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_2
-- name    : GenNewtonSubgrad.Composite.proposition_7_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:26.62692+00:00
-- url     : https://prove2.me/theorems/11a294d5-36db-45a2-b6c0-9a8ffdf9325f
-- title:
--   Proposition 7.2 — smoothness of the forward-backward envelope, gradient formula (7.4) and the equivalence (7.5)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be of class $C^2$ around $\bar x$, let $g:\mathbb R^n\to(-\infty,+\infty]$ be proper and prox-bounded, put $\varphi=f+g$, and suppose $0\in\partial\varphi(\bar x)$. Let $g$ be continuously prox-regular at $\bar x$ for $-\nabla f(\bar x)$ with modulus $r>0$. Write $\varphi_\gamma$ for the forward-backward envelope (7.2).
--
--   Then there is $\gamma_0\in(0,r^{-1}]$ such that for every $\gamma\in(0,\gamma_0)$ there is a neighbourhood $U$ of $\bar x$ with the following properties:
--
--   1. the prox-gradient mapping $x\mapsto\operatorname{Prox}_{\gamma g}(x-\gamma\nabla f(x))$ is single-valued on $U$, $\operatorname{Prox}_{\gamma g}(x-\gamma\nabla f(x))=\{P(x)\}$, and $P$ is Lipschitz continuous on $U$;
--   2. $\varphi_\gamma$ is finite and continuously differentiable on $U$, with
--   $$\nabla\varphi_\gamma(x)=\gamma^{-1}\big(I-\gamma\nabla^2f(x)\big)\big(x-\operatorname{Prox}_{\gamma g}(x-\gamma\nabla f(x))\big);\tag{7.4}$$
--   3. at every $x\in U$ at which $I-\gamma\nabla^2 f(x)$ is nonsingular,
--   $$\nabla\varphi_\gamma(x)=0\iff 0\in\partial\varphi(x).\tag{7.5}$$
--
--   The proposition makes the FBE a smooth surrogate whose stationary points are exactly those of $\varphi$; it is the first step in reducing the composite problem to the $C^{1,1}$ Newton method.
--
--   **Formalization Note** **Correction.** The paper claims these properties for every $\gamma\in(0,r^{-1})$. That is false: for $n=1$, $f=0$, $g(y)=\tfrac12y^2$ on $[-5,5]$, $g(y)=-1000-|y-10|$ on $[9,11]$, $g=+\infty$ elsewhere, $\bar x=0$, $r=1$ and $\gamma=\tfrac12$, one has $\operatorname{Prox}_{\gamma g}(x)=\{9\}$ for $x$ near $0$, so $\nabla\varphi_\gamma(0)=2(0-9)\neq0$ while $0\in\partial\varphi(0)$, contradicting (7.5). The proof cites Poliquin–Rockafellar, which gives the conclusions for $\gamma$ sufficiently small; the statement is posed in that form ($\exists\gamma_0\in(0,r^{-1}]$, $\forall\gamma\in(0,\gamma_0)$). "Nonsingular for $x\in U$" is read pointwise, as the proof uses it. Lower semicontinuity of $g$ around $\bar x$ is part of prox-regularity; properness of $g$ is the paper's standing convention $g:\mathbb R^n\to(-\infty,\infty]$. $\nabla^2f(x)$ is the derivative of $\nabla f$ at $x$. The final sentence (convex $g$, any $\gamma>0$) is not formalized: it is correct but unused. $\partial$ is the analytic limiting subdifferential, which agrees with the paper's (2.9) here because $\varphi$ is lower semicontinuous near $\bar x$.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 32, Proposition 7.2 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Proposition 7.2 (p. 32), corrected parameter range: for `f` of class `C²` around a
stationary point `x̄` of `φ = f + g`, and `g` proper, GenNewtonSubgrad.ProxReg.prox-bounded and continuously
GenNewtonSubgrad.ProxReg.prox-regular at `x̄` for `−∇f(x̄)` with modulus `r`, there is `γ₀ ∈ (0, r⁻¹]` such that for
every `γ ∈ (0, γ₀)` there is a neighbourhood `U` of `x̄` on which (i) the GenNewtonSubgrad.ProxReg.prox-gradient map is
single-valued and Lipschitz, (ii) the FBE is finite and continuously differentiable with gradient
(7.4), and (7.5) holds at every point where `I − γ∇²f(x)` is nonsingular. -/
theorem proposition_7_2 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EReal) (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hf : ∃ U₀ ∈ 𝓝 xbar, ContDiffOn ℝ 2 f U₀)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn f g) xbar)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(gradient f xbar)) r ε) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      ∃ U ∈ 𝓝 xbar, ∃ P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        -- (i) the GenNewtonSubgrad.ProxReg.prox-gradient mapping is single-valued and Lipschitz continuous on U
        (∀ x ∈ U, GenNewtonSubgrad.ProxReg.prox g γ (x - γ • gradient f x) = {P x}) ∧
        (∃ L, LipschitzOnWith L P U) ∧
        -- (ii) the FBE is finite and continuously differentiable on U, with gradient (7.4)
        (∀ x ∈ U, fbe f g γ x ≠ ⊤ ∧ fbe f g γ x ≠ ⊥) ∧
        (∀ x ∈ U, DifferentiableAt ℝ (fun z => (fbe f g γ z).toReal) x) ∧
        ContinuousOn (gradient (fun z => (fbe f g γ z).toReal)) U ∧
        (∀ x ∈ U, gradient (fun z => (fbe f g γ z).toReal) x =
          γ⁻¹ • ((x - P x) - γ • fderiv ℝ (gradient f) x (x - P x))) ∧
        -- (7.5) at every point of U where I − γ∇²f(x) is nonsingular
        (∀ x ∈ U, Function.Bijective
            (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - γ • fderiv ℝ (gradient f) x) →
          (gradient (fun z => (fbe f g γ z).toReal) x = 0 ↔
            0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn f g) x)) := by sorry

end GenNewtonSubgrad.Composite
