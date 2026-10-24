-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_4_i
-- name    : GenNewtonSubgrad.Composite.proposition_7_4_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:43.521975+00:00
-- url     : https://prove2.me/theorems/63a30acf-0fc1-419a-82b2-5f015802b2b8
-- title:
--   Proposition 7.4(i) — metric regularity of $\partial\varphi$ and of $\nabla\varphi_\gamma$ are equivalent
-- statement:
--   In the setting of Proposition 7.3 — $\varphi(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha+g(x)$ with $A$ symmetric and $g$ proper, prox-bounded and continuously prox-regular at $\bar x$ for $-A\bar x-b$ with modulus $r$, and $0\in\partial\varphi(\bar x)$ — let $\varphi_\gamma$ be the forward-backward envelope.
--
--   Then there is $\gamma_0\in(0,r^{-1}]$ such that for every $\gamma\in(0,\gamma_0)$ with $I-\gamma A$ nonsingular,
--   $$\partial\varphi\ \text{is metrically regular around }(\bar x,0)\iff\nabla\varphi_\gamma\ \text{is metrically regular around }\bar x .$$
--
--   This transfers the standing assumption (H2) from the subgradient mapping of the composite cost to the gradient of its envelope.
--
--   **Formalization Note** **Correction.** As printed, the equivalence is claimed for every $\gamma\in(0,r^{-1})$ with $I-\gamma A$ nonsingular, and that fails: for $n=1$, $A=0$, $b=0$, $g(y)=\tfrac12y^2$ on $[-5,5]$, $g(y)=-1000-20y$ on $[8,12]$, $g=+\infty$ elsewhere, $\bar x=0$, $r=1$, $\gamma=\tfrac12$, one has $\operatorname{Prox}_{\gamma g}(x)=\{x+10\}$ and $\nabla\varphi_\gamma\equiv-20$ near $0$, which is not metrically regular, while $\partial\varphi$ is the identity near $(0,0)$. The statement is posed for $\gamma$ sufficiently small. "$\nabla\varphi_\gamma$ metrically regular around $\bar x$" means around $(\bar x,\nabla\varphi_\gamma(\bar x))$, the convention for single-valued maps. Only assertion (i) is formalized; (ii) (tilt stability) is not used by Theorem 7.8. The conclusion also asserts that $\varphi_\gamma$ is finite and differentiable on a neighbourhood of $\bar x$, which the paper presupposes when it writes $\nabla\varphi_\gamma$ (Proposition 7.2(ii)); this rules out reading $\nabla\varphi_\gamma$ off the junk values of an infinite or nondifferentiable envelope.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 34, Proposition 7.4(i) (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Proposition 7.4(i) (p. 34), corrected parameter range: in the setting (7.7), for every small
`γ` with `I − γA` nonsingular, `∂φ` is metrically regular around `(x̄, 0)` if and only if the
gradient `∇φ_γ` of the FBE is metrically regular around `x̄`. -/
theorem proposition_7_4_i {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      (∃ U ∈ 𝓝 xbar, ∀ x ∈ U, fbe (quadF A b α) g γ x ≠ ⊤ ∧ fbe (quadF A b α) g γ x ≠ ⊥ ∧
        DifferentiableAt ℝ (fun y => (fbe (quadF A b α) g γ y).toReal) x) ∧
      (GenNewtonSubgrad.ProxReg.MetricRegularAround (NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g))
          xbar 0 ↔
        GenNewtonSubgrad.ProxReg.MetricRegularAround (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) xbar
          (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) xbar)) := by sorry

end GenNewtonSubgrad.Composite
