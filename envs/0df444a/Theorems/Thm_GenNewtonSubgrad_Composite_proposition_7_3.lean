-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_3
-- name    : GenNewtonSubgrad.Composite.proposition_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:30.25849+00:00
-- url     : https://prove2.me/theorems/98493e9f-15a7-4288-a513-91f8f764d5a4
-- title:
--   Proposition 7.3 — the generalized Hessian of the FBE, formula (7.8)
-- statement:
--   Let $\varphi(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha+g(x)$ on $\mathbb R^n$ as in (7.7): $A$ is a symmetric matrix, $b\in\mathbb R^n$, $\alpha\in\mathbb R$, and $g:\mathbb R^n\to(-\infty,+\infty]$ is proper, prox-bounded and continuously prox-regular at $\bar x$ for $-A\bar x-b$ with modulus $r>0$, where $0\in\partial\varphi(\bar x)$. Let $\varphi_\gamma$ be the forward-backward envelope (7.2) of $f+g$ with $f(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha$, and $B=I-\gamma A$.
--
--   Then there is $\gamma_0\in(0,r^{-1}]$ such that for every $\gamma\in(0,\gamma_0)$ with $B$ nonsingular there is a neighbourhood $U$ of $\bar x$ such that for every $x\in U$, with $u=x-\gamma(Ax+b)$, the proximal set $\operatorname{Prox}_{\gamma g}(u)$ is a single point $p$, and for all $w,z\in\mathbb R^n$
--   $$z\in\partial^2\varphi_\gamma(x)(w)\iff B^{-1}z-Aw\in\partial^2g\Big(\operatorname{Prox}_{\gamma g}(u),\frac1\gamma\big(u-\operatorname{Prox}_{\gamma g}(u)\big)\Big)\big(w-\gamma B^{-1}z\big).\tag{7.8}$$
--
--   The formula computes the generalized Hessian of the smooth surrogate $\varphi_\gamma$ from the data $A$ and $\partial^2 g$ alone; it is what turns the Newton step for $\varphi_\gamma$ into the implementable inclusion (7.18).
--
--   **Formalization Note** **Correction.** The paper claims the formula for every $\gamma\in(0,r^{-1})$ with $B$ nonsingular; its proof rests on Proposition 7.2 and Lemma 6.3, which hold only for $\gamma$ sufficiently small (counterexample in the note of Proposition 7.2). It is posed with $\exists\gamma_0\in(0,r^{-1}]$, $\forall\gamma\in(0,\gamma_0)$. The setting (7.7) includes stationarity $0\in\partial\varphi(\bar x)$, which is a hypothesis. $\partial^2\varphi_\gamma(x)(w)$ is the coderivative $D^*\nabla\varphi_\gamma(x)(w)$ of the gradient of the real-valued envelope ($\varphi_\gamma$ is $C^1$ near $\bar x$ by Proposition 7.2). The conclusion asserts $\operatorname{Prox}_{\gamma g}(u)=\{p\}$ so that "$\operatorname{Prox}_{\gamma g}(u)$" names a point without making the proximal mapping a function. $B^{-1}$ is `shiftInv A γ`, the inverse of $B$ when $B$ is bijective. A symmetric matrix is a self-adjoint operator on $\mathbb R^n$. The conclusion also asserts that $\varphi_\gamma$ is finite and differentiable on a neighbourhood of $\bar x$, which the paper presupposes when it writes $\nabla\varphi_\gamma$ (Proposition 7.2(ii)); this rules out reading $\nabla\varphi_\gamma$ off the junk values of an infinite or nondifferentiable envelope.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 33, Proposition 7.3, (7.8) (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Proposition 7.3 (p. 33), corrected parameter range: in the setting (7.7), for every small
`γ` with `B = I − γA` nonsingular, near `x̄` the generalized Hessian `∂²φ_γ(x) = D*∇φ_γ(x)` of the
FBE is given by (7.8) in terms of `∂²g` at `(Prox_γg(u), γ⁻¹(u − Prox_γg(u)))`, `u = x − γ(Ax + b)`. -/
theorem proposition_7_3 {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      ∃ U ∈ 𝓝 xbar, ∀ x ∈ U,
        (fbe (quadF A b α) g γ x ≠ ⊤ ∧ fbe (quadF A b α) g γ x ≠ ⊥ ∧
          DifferentiableAt ℝ (fun y => (fbe (quadF A b α) g γ y).toReal) x) ∧
        ∃ p : EuclideanSpace ℝ (Fin n), GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) = {p} ∧
        ∀ w z : EuclideanSpace ℝ (Fin n),
          z ∈ GenNewtonSubgrad.ProxReg.coderiv (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) x
              (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x) w ↔
            shiftInv A γ z - A w ∈
              GenNewtonSubgrad.ProxReg.secondSubdiff g p (γ⁻¹ • ((x - γ • (A x + b)) - p)) (w - γ • shiftInv A γ z) := by sorry

end GenNewtonSubgrad.Composite
