-- Prove2me | Theorems.Thm_NashFlowLT_SteadyState_uniform_slope
-- name    : NashFlowLT.SteadyState.uniform_slope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:26:36.260015+00:00
-- url     : https://prove2.me/theorems/dbfe6492-fe47-4a84-ac59-7e0a44281603
-- title:
--   Proof of Theorem 3, p. 12 — there is $\kappa>0$ with $\Phi'(\theta)\in\{0\}\cup[\kappa,\infty)$ almost everywhere
-- statement:
--   Let $(f^+,z)$ be a dynamic equilibrium in a fluid queuing network satisfying the standing assumptions, with potential $\Phi$. There is a constant $\kappa>0$ such that for almost every $\theta>0$, whenever $\Phi$ is differentiable at $\theta$,
--   $$\Phi'(\theta)=0\qquad\text{or}\qquad\Phi'(\theta)\ge\kappa .$$
--
--   Outside the steady state the potential grows at a uniform positive rate. Combined with a bound on $\Phi$, this forces the steady state to be reached in finite time.
--
--   **Formalization Note** The constant $\kappa$ may depend on the network and on the equilibrium; the page gives no explicit value.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, p. 12, proof of Theorem 3

import Mathlib
import Definitions.Def_NashFlowLT_SteadyState_Model

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Proof of Theorem 3, p. 12: there is `κ > 0` such that for almost every `θ > 0`, every derivative
of `Φ` at `θ` is either `0` or at least `κ`. -/
theorem uniform_slope (N : Network V E) (hN : N.Standing) (F : FlowOverTime V E)
    (hF : IsDynamicEquilibrium N F) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ θ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ d : ℝ,
      HasDerivAt (Phi N F) d θ → d = 0 ∨ κ ≤ d := by sorry
end NashFlowLT.SteadyState
