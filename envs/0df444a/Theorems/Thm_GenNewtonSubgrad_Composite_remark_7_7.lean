-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_remark_7_7
-- name    : GenNewtonSubgrad.Composite.remark_7_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:48:45.200745+00:00
-- url     : https://prove2.me/theorems/d1d6c339-f157-456b-94d4-9d81e2e1d600
-- title:
--   Remark 7.7 — Algorithm 7.6 is Algorithm 5.3 applied to the FBE $\varphi_\gamma$
-- statement:
--   In the setting of Proposition 7.3 (the composite cost (7.7) with $A$ symmetric and $g$ proper, prox-bounded and continuously prox-regular at the stationary point $\bar x$ for $-A\bar x-b$ with modulus $r$), let $\varphi_\gamma$ be the forward-backward envelope and $B=I-\gamma A$.
--
--   Then there is $\gamma_0\in(0,r^{-1}]$ such that for every $\gamma\in(0,\gamma_0)$ with $B$ nonsingular there is a neighbourhood $U$ of $\bar x$ such that for every $x\in U$, $u=x-\gamma(Ax+b)$ has a unique proximal point $v\in\operatorname{Prox}_{\gamma g}(u)$, and:
--
--   The stop tests agree: $0\in\partial\varphi(x)$ if and only if $\nabla\varphi_\gamma(x)=0$. A step of Algorithm 7.6 from $x$ is exactly a step of Algorithm 5.3 for $\varphi_\gamma$.
--
--   1. $\nabla\varphi_\gamma(x)=\frac1\gamma B(x-v)$;
--   2. for every direction $d$, the Newton inclusion (7.18) of Algorithm 7.6,
--   $$-\frac1\gamma(x-v)-Ad\in\partial^2g\Big(v,\frac1\gamma(u-v)\Big)(x-v+d),$$
--   holds if and only if $-\nabla\varphi_\gamma(x)\in\partial^2\varphi_\gamma(x)(d)$;
--   3. for every direction $d$, $-\nabla\varphi_\gamma(x)\in\partial^2\varphi_\gamma(x)(d)$ if and only if $-\nabla\varphi_\gamma(x)\in\partial\langle d,\nabla\varphi_\gamma\rangle(x)$, the Newton inclusion (5.3) of Algorithm 5.3 for $\varphi_\gamma$.
--
--   Hence near $\bar x$ a step of Algorithm 7.6 is a step of Algorithm 5.3 applied to $\varphi_\gamma$, which is how the paper transfers Theorem 5.7 to the composite problem.
--
--   **Formalization Note** **Correction.** As for Propositions 7.2 and 7.3, the remark rests on them and is posed for $\gamma$ sufficiently small ($\exists\gamma_0\in(0,r^{-1}]$, $\forall\gamma\in(0,\gamma_0)$) and near $\bar x$, rather than for every $\gamma\in(0,r^{-1})$ along the whole run. The item formalizes the remark's displayed equivalences: the gradient identity, the equivalence of (7.18) with $-\nabla\varphi_\gamma(x)\in\partial^2\varphi_\gamma(x)(d)$, and the scalarization (2.11). It also states proximal-point existence, the stop-test equivalence from Proposition 7.2, and equality of the algorithms' step relations, so the final reduction claim is explicit. $\partial^2\varphi_\gamma(x)$ is the coderivative $D^*\nabla\varphi_\gamma(x)$ of the gradient of the real-valued envelope. $\partial$ is the analytic limiting subdifferential; $x\mapsto\langle d,\nabla\varphi_\gamma(x)\rangle$ is continuous near $\bar x$, so it agrees with (2.9). The conclusion also asserts that $\varphi_\gamma$ is finite and differentiable on a neighbourhood of $\bar x$, which the paper presupposes when it writes $\nabla\varphi_\gamma$ (Proposition 7.2(ii)); this rules out reading $\nabla\varphi_\gamma$ off the junk values of an infinite or nondifferentiable envelope.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 35, Remark 7.7 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Alg76

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Remark 7.7 (p. 35), corrected parameter range: near `x̄`, for every proximal point
`v ∈ Prox_γg(u)`, `u = x − γ(Ax + b)`, one has `∇φ_γ(x) = γ⁻¹B(x − v)`; the Newton inclusion
(7.18) for a direction `d` is equivalent to `−∇φ_γ(x) ∈ ∂²φ_γ(x)(d)`, and that is equivalent to
`−∇φ_γ(x) ∈ ∂⟨d, ∇φ_γ⟩(x)`, so Algorithm 7.6 is Algorithm 5.3 for `φ_γ`. -/
theorem remark_7_7 {n : ℕ}
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
        (∃ p : EuclideanSpace ℝ (Fin n),
          GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) = {p}) ∧
        (0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) x ↔
          gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x = 0) ∧
        (∀ x' : EuclideanSpace ℝ (Fin n), alg76Step A b α g γ x x' ↔
          GenNewtonSubgrad.ProxReg.alg53Step
            (fun y => (fbe (quadF A b α) g γ y).toReal) x x') ∧
        ∀ v ∈ GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)),
        gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x = γ⁻¹ • shiftOp A γ (x - v) ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          -(γ⁻¹ • (x - v)) - A d ∈
              GenNewtonSubgrad.ProxReg.secondSubdiff g v (γ⁻¹ • ((x - γ • (A x + b)) - v)) (x - v + d) ↔
            -gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x ∈
              GenNewtonSubgrad.ProxReg.coderiv (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) x
                (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x) d) ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          -gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x ∈
              GenNewtonSubgrad.ProxReg.coderiv (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) x
                (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x) d ↔
            -gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x ∈
              NonconvexSplitting.Shared.LimitingSubdiff
                (fun z => ((⟪d, gradient (fun y => (fbe (quadF A b α) g γ y).toReal) z⟫_ℝ : ℝ) :
                  EReal)) x) := by sorry

end GenNewtonSubgrad.Composite
