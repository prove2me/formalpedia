-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_5
-- name    : GenNewtonSubgrad.Composite.proposition_7_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:38.213139+00:00
-- url     : https://prove2.me/theorems/1234c3c1-3f87-45a2-a5b8-206455fd75d3
-- title:
--   Proposition 7.5 — semismoothness* of $\partial g$ yields semismoothness* of $\nabla\varphi_\gamma$
-- statement:
--   In the setting of Proposition 7.4 — $\varphi(x)=\tfrac12\langle Ax,x\rangle+\langle b,x\rangle+\alpha+g(x)$ with $A$ symmetric and $g$ proper, prox-bounded and continuously prox-regular at $\bar x$ for $\bar v=-A\bar x-b$ with modulus $r$, and $0\in\partial\varphi(\bar x)$ — let $\varphi_\gamma$ be the forward-backward envelope.
--
--   Then there is $\gamma_0\in(0,r^{-1}]$ such that for every $\gamma\in(0,\gamma_0)$ with $I-\gamma A$ nonsingular: if the subgradient mapping $\partial g$ is semismooth\* at $(\bar x,\bar v)$, then the gradient mapping $\nabla\varphi_\gamma$ is semismooth\* at $\bar x$.
--
--   This transfers the standing assumption (H3) to the envelope, the last hypothesis needed to apply Theorem 5.7 to $\varphi_\gamma$.
--
--   **Formalization Note** **Correction.** The proposition inherits the parameter range of Propositions 7.2–7.4 and is posed for $\gamma$ sufficiently small ($\exists\gamma_0\in(0,r^{-1}]$, $\forall\gamma\in(0,\gamma_0)$); the printed range fails for the same reason (see Proposition 7.2). "$\nabla\varphi_\gamma$ semismooth\* at $\bar x$" is semismoothness\* of the single-valued map at $(\bar x,\nabla\varphi_\gamma(\bar x))$. The conclusion also asserts that $\varphi_\gamma$ is finite and differentiable on a neighbourhood of $\bar x$, which the paper presupposes when it writes $\nabla\varphi_\gamma$ (Proposition 7.2(ii)); this rules out reading $\nabla\varphi_\gamma$ off the junk values of an infinite or nondifferentiable envelope.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 35, Proposition 7.5 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Proposition 7.5 (p. 35), corrected parameter range: in the setting (7.7), for every small
`γ` with `I − γA` nonsingular, semismoothness* of `∂g` at `(x̄, −Ax̄ − b)` implies
semismoothness* of the FBE gradient `∇φ_γ` at `x̄`. -/
theorem proposition_7_5 {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      GenNewtonSubgrad.ProxReg.IsSemismoothStar (NonconvexSplitting.Shared.LimitingSubdiff g) xbar (-(A xbar + b)) →
      (∃ U ∈ 𝓝 xbar, ∀ x ∈ U, fbe (quadF A b α) g γ x ≠ ⊤ ∧ fbe (quadF A b α) g γ x ≠ ⊥ ∧
        DifferentiableAt ℝ (fun y => (fbe (quadF A b α) g γ y).toReal) x) ∧
      GenNewtonSubgrad.ProxReg.IsSemismoothStar (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) xbar
        (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) xbar) := by sorry

end GenNewtonSubgrad.Composite
